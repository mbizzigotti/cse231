importScripts('reference.js');

self.onmessage = function({ data: { prog, input } }) {
  const printed = [];
  const origLog = console.log;
  console.log = (...args) => printed.push(args.join(' '));
  try {
    const result = interpreter.run(prog, input);
    self.postMessage({ printed, result });
  } catch (e) {
    self.postMessage({ error: String(e.message ?? e) });
  } finally {
    console.log = origLog;
  }
};
