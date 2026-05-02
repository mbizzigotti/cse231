// Shared Diamondback program generation logic.
// Used by generator.html and batch.html.

const T_INT = 'int', T_BOOL = 'bool', T_ANY = 'any';

function pick(arr) { return arr[Math.floor(Math.random() * arr.length)]; }
function rand(lo, hi) { return Math.floor(Math.random() * (hi - lo + 1)) + lo; }
function gaussRand(mean, std) {
  const u = 1 - Math.random(), v = Math.random();
  return mean + std * Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * v);
}

let varCounter = 0, funCounter = 0, budget = 0;
function freshVar() { return `v${++varCounter}`; }
function freshFun() { return `f${++funCounter}`; }

function genExpr(env, want, allowInput, funs) {
  if (budget <= 0) return genLeaf(env, want, allowInput, funs);
  budget--;

  const forms = ['let', 'if', 'block', 'loop'];
  const setTargets = [...env.entries()].filter(([, t]) => want === T_ANY || t === want);
  if (setTargets.length > 0) forms.push('set!');

  if (want === T_INT || want === T_ANY)
    forms.push('add1', 'sub1', 'print_int', '+', '-', '*');
  if (want === T_BOOL || want === T_ANY)
    forms.push('isnum', 'isbool', 'print_bool', '<', '>', '>=', '<=', 'eq');
  for (const [name, fn] of funs)
    if (want === T_ANY || fn.retType === want) forms.push(`call:${name}`);

  const choice = pick(forms);
  switch (choice) {
    case 'let': {
      const n = rand(1, 3);
      const parts = [], newEnv = new Map(env);
      for (let i = 0; i < n; i++) {
        const vt = pick([T_INT, T_BOOL]), vn = freshVar();
        parts.push(`(${vn} ${genExpr(newEnv, vt, allowInput, funs)})`);
        newEnv.set(vn, vt);
      }
      return `(let (${parts.join(' ')}) ${genExpr(newEnv, want, allowInput, funs)})`;
    }
    case 'if':
      return `(if ${genExpr(env, T_BOOL, allowInput, funs)} ` +
                 `${genExpr(env, want, allowInput, funs)} ` +
                 `${genExpr(env, want, allowInput, funs)})`;
    case 'block': {
      const exprs = Array.from({length: rand(1, 3)}, () => genExpr(env, T_ANY, allowInput, funs));
      exprs.push(genExpr(env, want, allowInput, funs));
      return `(block ${exprs.join(' ')})`;
    }
    case 'loop': {
      const counter = freshVar(), limit = rand(1, 6);
      const newEnv = new Map([...env, [counter, T_INT]]);
      const breakVal = genExpr(newEnv, want, allowInput, funs);
      return `(let ((${counter} 0)) (loop (if (>= ${counter} ${limit}) ` +
             `(break ${breakVal}) (set! ${counter} (add1 ${counter})))))`;
    }
    case 'set!': {
      const [varName, varType] = pick(setTargets);
      return `(set! ${varName} ${genExpr(env, varType, allowInput, funs)})`;
    }
    case 'add1':       return `(add1 ${genExpr(env, T_INT, allowInput, funs)})`;
    case 'sub1':       return `(sub1 ${genExpr(env, T_INT, allowInput, funs)})`;
    case 'print_int':  return `(print ${genExpr(env, T_INT, allowInput, funs)})`;
    case 'print_bool': return `(print ${genExpr(env, T_BOOL, allowInput, funs)})`;
    case 'isnum':      return `(isnum ${genExpr(env, T_ANY, allowInput, funs)})`;
    case 'isbool':     return `(isbool ${genExpr(env, T_ANY, allowInput, funs)})`;
    case '+': case '-': case '*':
      return `(${choice} ${genExpr(env, T_INT, allowInput, funs)} ${genExpr(env, T_INT, allowInput, funs)})`;
    case '<': case '>': case '>=': case '<=':
      return `(${choice} ${genExpr(env, T_INT, allowInput, funs)} ${genExpr(env, T_INT, allowInput, funs)})`;
    case 'eq': {
      const at = pick([T_INT, T_BOOL]);
      return `(= ${genExpr(env, at, allowInput, funs)} ${genExpr(env, at, allowInput, funs)})`;
    }
    default: {
      const name = choice.slice(5), fn = funs.get(name);
      const args = fn.params.map(p => genExpr(env, p.type, allowInput, funs));
      return args.length ? `(${name} ${args.join(' ')})` : `(${name})`;
    }
  }
}

function genLeaf(env, want, allowInput, funs = new Map()) {
  const opts = [];
  if (want === T_INT || want === T_ANY) {
    opts.push(() => String(rand(0, 100)));
    if (allowInput) opts.push(() => 'input');
  }
  if (want === T_BOOL || want === T_ANY) opts.push(() => pick(['true', 'false']));
  for (const [name, type] of env)
    if (want === T_ANY || type === want) opts.push(() => name);
  for (const [name, fn] of funs)
    if (want === T_ANY || fn.retType === want)
      opts.push(() => {
        const args = fn.params.map(p => genLeaf(env, p.type, allowInput));
        return args.length ? `(${name} ${args.join(' ')})` : `(${name})`;
      });
  return pick(opts)();
}

function genSig() {
  return {
    name: freshFun(),
    params: Array.from({length: rand(0, 3)}, (_, i) => ({
      name: `p${i + 1}`,
      type: pick([T_INT, T_BOOL]),
    })),
    retType: pick([T_INT, T_BOOL]),
  };
}

function genBody(sig, funs) {
  const env = new Map(sig.params.map(p => [p.name, p.type]));
  return genExpr(env, sig.retType, false, funs);
}

// Resets all counters, generates one complete program, returns { prog, input }.
function generateOne(size) {
  varCounter = 0;
  funCounter = 0;
  budget = size;

  const meanFuns = budget / 10;
  const numFuns = Math.max(0, Math.round(gaussRand(meanFuns, Math.sqrt(meanFuns + 0.5))));
  const sigs = Array.from({length: numFuns}, genSig);
  const funs = new Map(sigs.map(s => [s.name, { params: s.params, retType: s.retType }]));

  const defns = sigs.map(sig => {
    const funsWithoutSelf = new Map([...funs].filter(([n]) => n !== sig.name));
    return { ...sig, body: genBody(sig, funsWithoutSelf) };
  });

  const lines = defns.map(({ name, params, body }) => {
    const ps = params.map(p => p.name).join(' ');
    return `(fun (${name}${ps ? ' ' + ps : ''}) ${body})`;
  });
  lines.push(genExpr(new Map(), T_ANY, true, funs));

  return { prog: lines.join('\n'), input: String(rand(-100, 100)) };
}

// Runs prog in a Web Worker and resolves with { printed, result } or rejects on
// error or timeout. Terminates the worker in all cases so loops can't leak.
function runWithTimeout(prog, input, ms = 3000) {
  return new Promise((resolve, reject) => {
    const worker = new Worker('worker.js');
    const timer = setTimeout(() => {
      worker.terminate();
      reject(new Error(`timed out after ${ms / 1000}s`));
    }, ms);
    worker.onmessage = ({ data }) => {
      clearTimeout(timer);
      worker.terminate();
      if (data.error) reject(new Error(data.error));
      else resolve(data);
    };
    worker.onerror = (e) => {
      clearTimeout(timer);
      worker.terminate();
      reject(new Error(e.message));
    };
    worker.postMessage({ prog, input });
  });
}
