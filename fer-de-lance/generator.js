// Random program generator for the fer-de-lance Lisp-like language.
//
// Every generated program comes with a known expected result, computed by an
// internal evaluator that mirrors the language's closure semantics:
//   * closures capture their free variables BY VALUE at definition time
//   * on call, those values are loaded into local variables
//   * set! mutates a local; mutations do not write back to the heap and are
//     never observable outside the function
//   * within a single function frame, set! on a let-bound local does mutate
//     that local (so block + set! + reference sees the new value)
//
// This lets the download-test flow build (.snek, expected) pairs without a
// reference interpreter.

/*
    Program Grammar:

    <expr> :=
    | true | false | nil | <number> | <identifier>
    | (let* (<binding>+) <expr>)
    | (let <binding> <expr>)
    | (<op1> <expr>)
    | (<op2> <expr> <expr>)
    | (set! <name> <expr>)
    | (if <expr> <expr> <expr>)
    | (block <expr>+)
    | (loop <expr>)
    | (break <expr>)
    | (fn (<arg>*) <expr>)
    | (defn (<name> <arg>*) <expr>)
    | (<name> <expr>*)
    | (vec <expr>+)
    | (vec-get <expr> <expr>)

    <op1> := add1 | sub1 | isnum | isbool | isvec
    <op2> := + | - | * | < | > | >= | <= | =
    <binding> := (<identifier> <expr>)
*/

// ============================================================
// Helpers
// ============================================================

const T_INT = 'int', T_BOOL = 'bool', T_VEC = 'vec';

function pick(arr) { return arr[Math.floor(Math.random() * arr.length)]; }
function rand(lo, hi) { return Math.floor(Math.random() * (hi - lo + 1)) + lo; }

let varCounter = 0;
function freshVar() { return `v${++varCounter}`; }

// ============================================================
// AST constructors
// ============================================================

const Int    = n           => ({ kind: 'int', value: n });
const Bool   = b           => ({ kind: 'bool', value: b });
const Nil    = ()          => ({ kind: 'nil' });
const Var    = name        => ({ kind: 'var', name });
const Let1   = (n, v, b)   => ({ kind: 'let1', name: n, value: v, body: b });
const LetStar= (bs, b)     => ({ kind: 'letstar', bindings: bs, body: b });
const Op1    = (op, a)     => ({ kind: 'op1', op, arg: a });
const Op2    = (op, l, r)  => ({ kind: 'op2', op, left: l, right: r });
const If_    = (c, t, e)   => ({ kind: 'if', cond: c, then: t, else: e });
const Block_ = exprs       => ({ kind: 'block', exprs });
const Loop_  = body        => ({ kind: 'loop', body });
const Break_ = expr        => ({ kind: 'break', expr });
const Set_   = (n, e)      => ({ kind: 'set', name: n, expr: e });
const Fn_    = (ps, b)     => ({ kind: 'fn', params: ps, body: b });
const Defn_  = (n, ps, b)  => ({ kind: 'defn', name: n, params: ps, body: b });
const Call_  = (n, args)   => ({ kind: 'call', name: n, args });
const Vec_   = elems       => ({ kind: 'vec', elems });
const VecGet = (v, i)      => ({ kind: 'vecget', vec: v, idx: i });

// ============================================================
// Free-variable analysis (used at closure-creation time)
// ============================================================

function freeVars(ast, bound = new Set()) {
  const fv = new Set();
  (function walk(n, b) {
    switch (n.kind) {
      case 'int': case 'bool': case 'nil': return;
      case 'var':
        if (!b.has(n.name)) fv.add(n.name); return;
      case 'let1': {
        walk(n.value, b);
        const b2 = new Set(b); b2.add(n.name);
        walk(n.body, b2); return;
      }
      case 'letstar': {
        let b2 = new Set(b);
        for (const { name, value } of n.bindings) {
          walk(value, b2);
          b2 = new Set(b2); b2.add(name);
        }
        walk(n.body, b2); return;
      }
      case 'op1': walk(n.arg, b); return;
      case 'op2': walk(n.left, b); walk(n.right, b); return;
      case 'if':  walk(n.cond, b); walk(n.then, b); walk(n.else, b); return;
      case 'block': for (const e of n.exprs) walk(e, b); return;
      case 'loop':  walk(n.body, b); return;
      case 'break': walk(n.expr, b); return;
      case 'set':
        if (!b.has(n.name)) fv.add(n.name);
        walk(n.expr, b); return;
      case 'fn': {
        const b2 = new Set(b); for (const p of n.params) b2.add(p);
        walk(n.body, b2); return;
      }
      case 'defn': {
        const b2 = new Set(b); b2.add(n.name);
        for (const p of n.params) b2.add(p);
        walk(n.body, b2); return;
      }
      case 'call':
        if (!b.has(n.name)) fv.add(n.name);
        for (const a of n.args) walk(a, b); return;
      case 'vec': for (const e of n.elems) walk(e, b); return;
      case 'vecget': walk(n.vec, b); walk(n.idx, b); return;
    }
  })(ast, bound);
  return fv;
}

// ============================================================
// Evaluator — snapshot-capture closure semantics
// ============================================================
//
// Runtime values:
//   integer  -> JS number
//   bool     -> JS boolean
//   nil      -> NIL sentinel
//   vec      -> { kind: 'vec-value', elems: [...] }
//   closure  -> { kind: 'fun', params, body, captures }
//
// A FRAME is a Map<name, value>. Each function call gets its own frame
// initialised from (captures + params); let / let* mutate the current frame
// on entry and restore on exit. set! mutates the binding in the current
// frame in place — never reaching an outer frame.

const NIL = Object.freeze({ kind: 'nil-value' });

function isInt (v) { return typeof v === 'number' && Number.isInteger(v); }
function isBool(v) { return typeof v === 'boolean'; }
function isVec (v) { return v !== null && typeof v === 'object' && v.kind === 'vec-value'; }
function isFun (v) { return v !== null && typeof v === 'object' && v.kind === 'fun'; }
function describeVal(v) {
  if (v === NIL) return 'nil';
  if (isInt(v))  return 'int';
  if (isBool(v)) return 'bool';
  if (isVec(v))  return 'vec';
  if (isFun(v))  return 'fun';
  return 'unknown';
}
function need(v, pred, want) {
  if (!pred(v)) throw new Error(`expected ${want}, got ${describeVal(v)}`);
}

class BreakSignal { constructor(value) { this.value = value; } }

const MAX_STEPS = 100_000;
const MAX_DEPTH = 500;
const MAX_LOOP_ITERS = 10_000;

let evalSteps = 0;
let evalDepth = 0;

function evalAst(ast, frame) {
  if (++evalSteps > MAX_STEPS) throw new Error('eval step limit');
  if (evalDepth > MAX_DEPTH)   throw new Error('eval depth limit');
  evalDepth++;
  try { return evalInner(ast, frame); }
  finally { evalDepth--; }
}

function evalInner(ast, frame) {
  switch (ast.kind) {
    case 'int':  return ast.value;
    case 'bool': return ast.value;
    case 'nil':  return NIL;

    case 'var': {
      if (!frame.has(ast.name)) throw new Error(`unbound: ${ast.name}`);
      return frame.get(ast.name);
    }

    case 'let1': {
      const v = evalAst(ast.value, frame);
      return withBinding(frame, ast.name, v, () => evalAst(ast.body, frame));
    }

    case 'letstar': {
      const saved = [];
      for (const { name, value } of ast.bindings) {
        const v = evalAst(value, frame);
        saved.push({ name, had: frame.has(name), old: frame.get(name) });
        frame.set(name, v);
      }
      try { return evalAst(ast.body, frame); }
      finally {
        for (let i = saved.length - 1; i >= 0; i--) {
          const { name, had, old } = saved[i];
          if (had) frame.set(name, old); else frame.delete(name);
        }
      }
    }

    case 'op1': {
      const v = evalAst(ast.arg, frame);
      switch (ast.op) {
        case 'add1':   need(v, isInt, 'int'); return v + 1;
        case 'sub1':   need(v, isInt, 'int'); return v - 1;
        case 'isnum':  return isInt(v);
        case 'isbool': return isBool(v);
        case 'isvec':  return isVec(v);
        default: throw new Error(`unknown op1: ${ast.op}`);
      }
    }

    case 'op2': {
      const l = evalAst(ast.left,  frame);
      const r = evalAst(ast.right, frame);
      switch (ast.op) {
        case '+':  need(l, isInt, 'int'); need(r, isInt, 'int'); return l + r;
        case '-':  need(l, isInt, 'int'); need(r, isInt, 'int'); return l - r;
        case '*':  need(l, isInt, 'int'); need(r, isInt, 'int'); return l * r;
        case '<':  need(l, isInt, 'int'); need(r, isInt, 'int'); return l <  r;
        case '>':  need(l, isInt, 'int'); need(r, isInt, 'int'); return l >  r;
        case '<=': need(l, isInt, 'int'); need(r, isInt, 'int'); return l <= r;
        case '>=': need(l, isInt, 'int'); need(r, isInt, 'int'); return l >= r;
        case '=': {
          if (describeVal(l) !== describeVal(r))
            throw new Error('= on different types');
          if (isVec(l) || isFun(l))
            throw new Error('= on non-scalar');
          return l === r;
        }
        default: throw new Error(`unknown op2: ${ast.op}`);
      }
    }

    case 'if': {
      const c = evalAst(ast.cond, frame);
      need(c, isBool, 'bool');
      return c ? evalAst(ast.then, frame) : evalAst(ast.else, frame);
    }

    case 'block': {
      let v = NIL;
      for (const e of ast.exprs) v = evalAst(e, frame);
      return v;
    }

    case 'loop': {
      let i = 0;
      for (;;) {
        if (++i > MAX_LOOP_ITERS) throw new Error('loop iter limit');
        try { evalAst(ast.body, frame); }
        catch (e) {
          if (e instanceof BreakSignal) return e.value;
          throw e;
        }
      }
    }

    case 'break':
      throw new BreakSignal(evalAst(ast.expr, frame));

    case 'set': {
      if (!frame.has(ast.name)) throw new Error(`set! unbound: ${ast.name}`);
      const v = evalAst(ast.expr, frame);
      frame.set(ast.name, v);
      return v;
    }

    case 'fn': {
      const fv = freeVars(ast);
      const captures = {};
      for (const name of fv) {
        if (!frame.has(name)) throw new Error(`fn free var unbound: ${name}`);
        captures[name] = frame.get(name);
      }
      return { kind: 'fun', params: ast.params, body: ast.body, captures };
    }

    case 'defn': {
      const fv = freeVars(ast);
      const captures = {};
      for (const name of fv) {
        if (!frame.has(name)) throw new Error(`defn free var unbound: ${name}`);
        captures[name] = frame.get(name);
      }
      const closure = { kind: 'fun', params: ast.params, body: ast.body, captures };
      captures[ast.name] = closure;
      return closure;
    }

    case 'call': {
      if (!frame.has(ast.name)) throw new Error(`call unbound: ${ast.name}`);
      const fn = frame.get(ast.name);
      need(fn, isFun, 'fun');
      if (fn.params.length !== ast.args.length)
        throw new Error(`arity mismatch on ${ast.name}`);
      const argVals = ast.args.map(a => evalAst(a, frame));
      const newFrame = new Map();
      for (const [k, v] of Object.entries(fn.captures)) newFrame.set(k, v);
      for (let i = 0; i < fn.params.length; i++)
        newFrame.set(fn.params[i], argVals[i]);
      return evalAst(fn.body, newFrame);
    }

    case 'vec':
      return { kind: 'vec-value', elems: ast.elems.map(e => evalAst(e, frame)) };

    case 'vecget': {
      const v = evalAst(ast.vec, frame);
      need(v, isVec, 'vec');
      const i = evalAst(ast.idx, frame);
      need(i, isInt, 'int');
      if (i < 0 || i >= v.elems.length) throw new Error('vec index out of bounds');
      return v.elems[i];
    }

    default: throw new Error(`unknown node: ${ast.kind}`);
  }
}

function withBinding(frame, name, value, k) {
  const had = frame.has(name);
  const old = frame.get(name);
  frame.set(name, value);
  try { return k(); }
  finally {
    if (had) frame.set(name, old);
    else frame.delete(name);
  }
}

function formatValue(v) {
  if (v === NIL) return 'nil';
  if (isInt(v))  return String(v);
  if (isBool(v)) return v ? 'true' : 'false';
  if (isVec(v))  return `(vec ${v.elems.map(formatValue).join(' ')})`;
  if (isFun(v))  return '<closure>';
  return String(v);
}

// ============================================================
// Serializer — AST -> fer-de-lance source string
// ============================================================

// Entry point: unfolds top-level Let1(name, Defn(name, ...), body) chains
// into the `(defn ...) (body)` statement-sequence sugar. Only valid at the
// very top of the program — `serialize` itself never emits the sugar, so a
// Let1+Defn appearing in a nested position serializes as a regular let.
function serializeProgram(ast) {
  if (ast.kind === 'let1' && ast.value.kind === 'defn' && ast.value.name === ast.name) {
    return `${serialize(ast.value)}\n${serializeProgram(ast.body)}`;
  }
  return serialize(ast);
}

function serialize(ast) {
  switch (ast.kind) {
    case 'int':  return String(ast.value);
    case 'bool': return ast.value ? 'true' : 'false';
    case 'nil':  return 'nil';
    case 'var':  return ast.name;

    case 'let1':
      return `(let (${ast.name} ${serialize(ast.value)}) ${serialize(ast.body)})`;
    case 'letstar': {
      const bs = ast.bindings
        .map(({ name, value }) => `(${name} ${serialize(value)})`)
        .join(' ');
      return `(let* (${bs}) ${serialize(ast.body)})`;
    }
    case 'op1': return `(${ast.op} ${serialize(ast.arg)})`;
    case 'op2': return `(${ast.op} ${serialize(ast.left)} ${serialize(ast.right)})`;
    case 'if':
      return `(if ${serialize(ast.cond)} ${serialize(ast.then)} ${serialize(ast.else)})`;
    case 'block':
      return `(block ${ast.exprs.map(serialize).join(' ')})`;
    case 'loop':  return `(loop ${serialize(ast.body)})`;
    case 'break': return `(break ${serialize(ast.expr)})`;
    case 'set':   return `(set! ${ast.name} ${serialize(ast.expr)})`;
    case 'fn':    return `(fn (${ast.params.join(' ')}) ${serialize(ast.body)})`;
    case 'defn':
      return `(defn (${[ast.name, ...ast.params].join(' ')}) ${serialize(ast.body)})`;
    case 'call':
      return ast.args.length
        ? `(${ast.name} ${ast.args.map(serialize).join(' ')})`
        : `(${ast.name})`;
    case 'vec':    return `(vec ${ast.elems.map(serialize).join(' ')})`;
    case 'vecget': return `(vec-get ${serialize(ast.vec)} ${serialize(ast.idx)})`;
  }
}

// ============================================================
// Filler — small type-directed random expressions for template holes
// ============================================================
//
// env: Map<name, type-string>  ('int' | 'bool' | 'vec')
// Filler stays in the pure subset (no closures of its own), but at int
// positions it may delegate to a full closure-test template — that's how
// test cases nest inside each other. The `nestingDepth` / `maxNestDepth`
// counter caps how many levels of nesting one program may contain.

let nestingDepth = 0;
let maxNestDepth = 0;
const NEST_PROB = 0.15;

function genFiller(env, want, budget) {
  if (want === T_INT && nestingDepth < maxNestDepth && Math.random() < NEST_PROB) {
    nestingDepth++;
    try { return pick(TEMPLATES)(); }
    finally { nestingDepth--; }
  }
  if (budget <= 0) return genFillerLeaf(env, want);

  const opts = [];
  opts.push(() => genFillerLeaf(env, want));
  opts.push(() => If_(
    genFiller(env, T_BOOL, Math.floor(budget / 3)),
    genFiller(env, want,   Math.floor(budget / 3)),
    genFiller(env, want,   Math.floor(budget / 3)),
  ));
  opts.push(() => {
    const vt = pick([T_INT, T_BOOL]);
    const vn = freshVar();
    const val = genFiller(env, vt, Math.floor(budget / 2));
    const newEnv = new Map([...env, [vn, vt]]);
    return Let1(vn, val, genFiller(newEnv, want, Math.floor(budget / 2)));
  });

  if (want === T_INT) {
    opts.push(() => Op1(pick(['add1', 'sub1']),
      genFiller(env, T_INT, budget - 1)));
    opts.push(() => Op2(pick(['+', '-', '*']),
      genFiller(env, T_INT, Math.floor(budget / 2)),
      genFiller(env, T_INT, Math.floor(budget / 2))));
  }
  if (want === T_BOOL) {
    opts.push(() => Op2(pick(['<', '>', '<=', '>=']),
      genFiller(env, T_INT, Math.floor(budget / 2)),
      genFiller(env, T_INT, Math.floor(budget / 2))));
    opts.push(() => Op2('=',
      genFiller(env, T_INT, Math.floor(budget / 2)),
      genFiller(env, T_INT, Math.floor(budget / 2))));
    opts.push(() => Op1(pick(['isnum', 'isbool', 'isvec']),
      genFiller(env, pick([T_INT, T_BOOL]), Math.floor(budget / 2))));
  }
  if (want === T_VEC) {
    opts.push(() => Vec_(Array.from(
      { length: rand(1, 3) },
      () => genFiller(env, pick([T_INT, T_BOOL]), Math.floor(budget / 3))
    )));
  }
  return pick(opts)();
}

function genFillerLeaf(env, want) {
  const opts = [];
  if (want === T_INT)  opts.push(() => Int(rand(-50, 50)));
  if (want === T_BOOL) opts.push(() => Bool(pick([true, false])));
  if (want === T_VEC)  opts.push(() => Vec_([
    Int(rand(-10, 10)), Int(rand(-10, 10)),
  ]));
  for (const [name, type] of env) {
    if (type === want) opts.push(() => Var(name));
  }
  return pick(opts)();
}

// ============================================================
// Closure-test templates
// ============================================================

// 1. Capture-at-definition: closure sees x's value at the moment it was made,
//    not the value x has when the closure is called.
function tmplCaptureTiming() {
  const aExpr = genFiller(new Map(), T_INT, 3);
  const bExpr = genFiller(new Map(), T_INT, 3);
  return Let1('x', aExpr,
    Let1('f', Fn_([], Var('x')),
      Block_([Set_('x', bExpr), Call_('f', [])])));
}

// 2. Capture isolation: set! inside the fn touches only the fn's own local.
//    The outer x is observably unchanged afterwards.
function tmplCaptureIsolation() {
  const aExpr = genFiller(new Map(), T_INT, 3);
  const bExpr = genFiller(new Map(), T_INT, 3);
  const cExpr = genFiller(new Map(), T_INT, 3);
  return Let1('x', aExpr,
    Let1('f', Fn_([], Block_([Set_('x', bExpr), cExpr])),
      Block_([Call_('f', []), Var('x')])));
}

// 3. Shadowing: closure captures the binding visible at definition time,
//    not a later inner shadowing.
function tmplShadowingCapture() {
  const aExpr = genFiller(new Map(), T_INT, 3);
  const bExpr = genFiller(new Map(), T_INT, 3);
  return Let1('x', aExpr,
    Let1('f', Fn_([], Var('x')),
      Let1('x', bExpr, Call_('f', []))));
}

// 4. Adder factory: two closures each carry their own captured `n`.
function tmplAdderFactory() {
  const n1 = genFiller(new Map(), T_INT, 2);
  const n2 = genFiller(new Map(), T_INT, 2);
  const xv = genFiller(new Map(), T_INT, 2);
  const yv = genFiller(new Map(), T_INT, 2);
  return Let1('mk',
    Fn_(['n'], Fn_(['x'], Op2('+', Var('x'), Var('n')))),
    LetStar(
      [{ name: 'a', value: Call_('mk', [n1]) },
       { name: 'b', value: Call_('mk', [n2]) }],
      Op2('+', Call_('a', [xv]), Call_('b', [yv])),
    ));
}

// 5. Higher-order apply: closure passed as an argument, called by parameter
//    name inside the callee.
function tmplHigherOrderApply() {
  const inputVal = genFiller(new Map(), T_INT, 2);
  const gBody = genFiller(new Map([['y', T_INT]]), T_INT, 4);
  return Let1('apply',
    Fn_(['f', 'x'], Call_('f', [Var('x')])),
    Let1('g', Fn_(['y'], gBody),
      Call_('apply', [Var('g'), inputVal])));
}

// 6. Recursive countdown via defn — bounded, exercises self-reference.
function tmplRecursiveCountdown() {
  const n = rand(1, 10);
  return Let1('down',
    Defn_('down', ['n', 'acc'],
      If_(Op2('=', Var('n'), Int(0)),
        Var('acc'),
        Call_('down', [
          Op1('sub1', Var('n')),
          Op2('+', Var('acc'), Var('n')),
        ]))),
    Call_('down', [Int(n), Int(0)]));
}

// 7. Captured vec: a vec value lives in the closure's captures.
function tmplCapturedVec() {
  const a = genFiller(new Map(), T_INT, 2);
  const b = genFiller(new Map(), T_INT, 2);
  const c = genFiller(new Map(), T_INT, 2);
  return Let1('v', Vec_([a, b, c]),
    Let1('f', Fn_(['i'], VecGet(Var('v'), Var('i'))),
      Op2('+', Call_('f', [Int(0)]), Call_('f', [Int(2)]))));
}

// 8. Vec of closures: closures stored in a tuple, fetched out, then called.
//    Grammar requires a name in the call position, so we let-bind the
//    vec-get result before invoking.
function tmplVecOfClosures() {
  const a = genFiller(new Map(), T_INT, 2);
  const b = genFiller(new Map(), T_INT, 2);
  const c = genFiller(new Map(), T_INT, 2);
  return Let1('mk', Fn_(['n'], Fn_([], Var('n'))),
    Let1('vs', Vec_([
      Call_('mk', [a]),
      Call_('mk', [b]),
      Call_('mk', [c]),
    ]),
      Let1('k', VecGet(Var('vs'), Int(1)), Call_('k', []))));
}

const TEMPLATES = [
  tmplCaptureTiming,
  tmplCaptureIsolation,
  tmplShadowingCapture,
  tmplAdderFactory,
  tmplHigherOrderApply,
  tmplRecursiveCountdown,
  tmplCapturedVec,
  tmplVecOfClosures,
];

// ============================================================
// Top-level
// ============================================================

// genProgram returns { source, input, printed, result }.
//   complexity: how many additional templates may nest inside the outer one.
//     0 = single template (default), 1 = one extra level, etc. Capped at 4
//     internally because nesting grows the AST roughly geometrically.
// `input` is always "0" — the generated language no longer reads input.
// `printed` is always empty — fer-de-lance has no print form.
// `result` is the formatted final value.
function genProgram(complexity = 0) {
  const requested = Math.max(0, Math.min(4, Math.floor(complexity)));
  let lastErr = null;
  for (let attempt = 0; attempt < 20; attempt++) {
    varCounter = 0;
    evalSteps = 0;
    evalDepth = 0;
    nestingDepth = 0;
    maxNestDepth = requested;
    const template = pick(TEMPLATES);
    const ast = template();
    try {
      const value = evalAst(ast, new Map());
      return {
        source:  serializeProgram(ast),
        input:   '0',
        printed: [],
        result:  formatValue(value),
      };
    } catch (e) {
      lastErr = e;
    }
  }
  throw new Error(`failed to generate a valid program: ${lastErr && lastErr.message}`);
}
