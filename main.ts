// Tiny stack VM for make.fun's tiny stack ISA v1. Dispatch is a handler
// table indexed by opcode; stack, call stack and memory are Int32Arrays
// so every value wraps as int32, and output goes into one preallocated
// 64 KiB buffer (no per-byte allocations on PUTC-heavy programs).
import { readdirSync, readFileSync, mkdirSync, writeFileSync, statSync } from 'node:fs';
import { join } from 'node:path';

const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Per-opcode metadata: immediate length (-1 = unknown), pops, pushes.
const IMM = new Int8Array(256).fill(-1), POP = new Int8Array(256), PSH = new Int8Array(256);
const def = (op, imm, pops, pushes) => { IMM[op] = imm; POP[op] = pops; PSH[op] = pushes; };
def(0x00, 0, 0, 0); def(0x01, 1, 0, 1); def(0x02, 4, 0, 1); def(0x03, 0, 1, 0);
def(0x04, 0, 1, 2); def(0x05, 0, 2, 2); def(0x06, 0, 2, 3); def(0x07, 0, 3, 3);
for (const op of [0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x18, 0x19, 0x1a, 0x1c, 0x1d, 0x1e, 0x20, 0x21, 0x22]) def(op, 0, 2, 1);
def(0x17, 0, 1, 1); def(0x1b, 0, 1, 1);
def(0x30, 2, 0, 0); def(0x31, 2, 1, 0); def(0x32, 2, 1, 0); def(0x33, 2, 0, 0); def(0x34, 0, 0, 0);
def(0x40, 0, 1, 1); def(0x41, 0, 2, 0);
def(0x50, 0, 1, 0); def(0x51, 0, 1, 0); def(0x52, 0, 0, 1); def(0x53, 0, 1, 0);

const sgn16 = (v) => (v >= 32768 ? v - 65536 : v);
const bin = (f) => (s) => { const b = s.st[--s.sp], a = s.st[--s.sp]; s.st[s.sp++] = f(a, b); return s.nx; };
const un = (f) => (s) => { s.st[s.sp - 1] = f(s.st[s.sp - 1]); return s.nx; };

// Each handler returns the next pc, or throws {t: trap} / {x: exit}.
const H = new Array(256);
H[0x00] = () => { throw { x: 0 }; };
H[0x01] = (s) => { s.st[s.sp++] = s.raw < 128 ? s.raw : s.raw - 256; return s.nx; };
H[0x02] = (s) => { s.st[s.sp++] = s.raw | 0; return s.nx; };
H[0x03] = (s) => { s.sp--; return s.nx; };
H[0x04] = (s) => { s.st[s.sp] = s.st[s.sp - 1]; s.sp++; return s.nx; };
H[0x05] = (s) => { const t = s.st[s.sp - 1]; s.st[s.sp - 1] = s.st[s.sp - 2]; s.st[s.sp - 2] = t; return s.nx; };
H[0x06] = (s) => { s.st[s.sp] = s.st[s.sp - 2]; s.sp++; return s.nx; };
H[0x07] = (s) => { const a = s.st[s.sp - 3]; s.st[s.sp - 3] = s.st[s.sp - 2]; s.st[s.sp - 2] = s.st[s.sp - 1]; s.st[s.sp - 1] = a; return s.nx; };
H[0x10] = bin((a, b) => (a + b) | 0);
H[0x11] = bin((a, b) => (a - b) | 0);
H[0x12] = bin((a, b) => Math.imul(a, b));
H[0x13] = bin((a, b) => { if (b === 0) throw { t: 4 }; if (a === -2147483648 && b === -1) return a; return ((a - (a % b)) / b) | 0; });
H[0x14] = bin((a, b) => { if (b === 0) throw { t: 4 }; return (a % b) | 0; });
H[0x15] = bin((a, b) => { const ub = b >>> 0; if (ub === 0) throw { t: 4 }; const ua = a >>> 0; return ((ua - (ua % ub)) / ub) | 0; });
H[0x16] = bin((a, b) => { const ub = b >>> 0; if (ub === 0) throw { t: 4 }; return ((a >>> 0) % ub) | 0; });
H[0x17] = un((a) => (-a) | 0);
H[0x18] = bin((a, b) => a & b);
H[0x19] = bin((a, b) => a | b);
H[0x1a] = bin((a, b) => a ^ b);
H[0x1b] = un((a) => ~a);
H[0x1c] = bin((a, b) => a << (b & 31));
H[0x1d] = bin((a, b) => a >> (b & 31));
H[0x1e] = bin((a, b) => (a >>> (b & 31)) | 0);
H[0x20] = bin((a, b) => (a === b ? 1 : 0));
H[0x21] = bin((a, b) => (a < b ? 1 : 0));
H[0x22] = bin((a, b) => ((a >>> 0) < (b >>> 0) ? 1 : 0));
H[0x30] = (s) => s.nx + sgn16(s.raw);
H[0x31] = (s) => (s.st[--s.sp] === 0 ? s.nx + sgn16(s.raw) : s.nx);
H[0x32] = (s) => (s.st[--s.sp] !== 0 ? s.nx + sgn16(s.raw) : s.nx);
H[0x33] = (s) => { if (s.cp >= 64) throw { t: 7 }; s.cs[s.cp++] = s.nx; return s.raw; };
H[0x34] = (s) => { if (s.cp === 0) throw { t: 8 }; return s.cs[--s.cp]; };
H[0x40] = (s) => { const a = s.st[s.sp - 1]; if (a < 0 || a > 255) throw { t: 6 }; s.st[s.sp - 1] = s.mem[a]; return s.nx; };
H[0x41] = (s) => { const a = s.st[--s.sp], v = s.st[--s.sp]; if (a < 0 || a > 255) throw { t: 6 }; s.mem[a] = v; return s.nx; };
H[0x50] = (s) => { const t = String(s.st[--s.sp]); if (s.olen + t.length > 65536) throw { t: 11 }; s.olen += s.ob.write(t, s.olen, 'ascii'); return s.nx; };
H[0x51] = (s) => { const v = s.st[--s.sp]; if (s.olen >= 65536) throw { t: 11 }; s.ob[s.olen++] = v & 255; return s.nx; };
H[0x52] = (s) => { s.st[s.sp++] = s.ii < s.inp.length ? s.inp[s.ii++] : -1; return s.nx; };
H[0x53] = (s) => { throw { x: s.st[s.sp - 1] & 255 }; };

function run(prog, inp) {
  const s = {
    st: new Int32Array(256), sp: 0, cs: new Int32Array(64), cp: 0,
    mem: new Int32Array(256), inp, ii: 0,
    ob: Buffer.alloc(65536), olen: 0, nx: 0, raw: 0,
  };
  let steps = 0, pc = 0;
  try {
    for (;;) {
      if (steps >= 1000000) throw { t: 10 };
      if (pc < 0 || pc >= prog.length) throw { t: 9 };
      const op = prog[pc], il = IMM[op];
      if (il < 0) throw { t: 5 };
      if (pc + 1 + il > prog.length) throw { t: 9 };
      steps++;
      if (s.sp < POP[op]) throw { t: 2 };
      if (s.sp - POP[op] + PSH[op] > 256) throw { t: 3 };
      s.nx = pc + 1 + il;
      let raw = 0;
      for (let k = 0; k < il; k++) raw |= prog[pc + 1 + k] << (8 * k);
      s.raw = raw;
      pc = H[op](s);
    }
  } catch (e) {
    if (e !== null && typeof e === 'object' && ('t' in e || 'x' in e)) {
      return { out: s.ob.subarray(0, s.olen), exit: 't' in e ? e.t : e.x };
    }
    throw e;
  }
}

for (const id of readdirSync(IN_DIR).sort()) {
  const dir = join(IN_DIR, id);
  let isDir = false;
  try { isDir = statSync(dir).isDirectory(); } catch { /* not an instance */ }
  if (!isDir) continue;
  let prog, inp;
  try { prog = readFileSync(join(dir, 'program.bin')); } catch { prog = Buffer.alloc(0); }
  try { inp = readFileSync(join(dir, 'input.bin')); } catch { inp = Buffer.alloc(0); }
  const r = run(prog, inp);
  const od = join(OUT_DIR, id);
  mkdirSync(od, { recursive: true });
  writeFileSync(join(od, 'stdout.bin'), r.out);
  writeFileSync(join(od, 'exit.txt'), String(r.exit));
}
