const { interpreter } = require('./reference.js');

const prog = `(fun (sum n total)
	(if (= n 0)
		total
		(loop(break(sum (sub1 n) (+ total n))))
	)
)
(sum 10000 0)`;

const printed = [];
const origLog = console.log;
console.log = (...args) => printed.push(args.join(' '));

try {
  const result = interpreter.run(prog, '0');
  console.log = origLog;
  if (printed.length) console.log('printed:', printed);
  console.log('result:', result);
} catch(e) {
  console.log = origLog;
  console.log('error:', String(e.message ?? e));
}
