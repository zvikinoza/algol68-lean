# Verification

`a68lean` is written in Lean 4 so that as much as possible of it is
*checkable*: definitions are total functions accepted by Lean's termination
checker, data is immutable, and the properties that carry the most risk are
stated as theorems and proved. `lake build` elaborates every theorem; a build
that succeeds is the certificate.

## What is proved

### A verified compiler for the expression core (`A68/Verified/StackMachine.lean`)

The strategy used to compile formulas — evaluate operands onto an operand stack,
then apply the operator; identity declarations push an environment slot — is
isolated as a small language and proved correct against a stack machine:

```lean
theorem compile_correct (e : Expr) (st env : List Int) :
    exec (compile e) ⟨st, env⟩ = ⟨e.eval env :: st, env⟩
```

For every expression, every initial stack and every environment, running the
compiled code leaves exactly the expression's value on top of the stack and
the environment unchanged. Corollaries: `run_compile` (a closed expression
yields a singleton stack) and `compile_length` (code size is linear in the
expression size). The proof is by structural induction with `exec_append`.

### Exact decimal arithmetic (`A68/Verified/Numfmt.lean`)

Byte-exact number formatting rests on the decimal type `Dec = mant × 10^exp`
used by `whole`, `fixed` and `float`. With `valAt d e` the integer value of `d`
scaled to a common exponent `e`, the following are proved:

```lean
theorem Dec.valAt_add   : valAt (add a b) e = valAt a e + valAt b e     -- e ≤ a.exp, e ≤ b.exp
theorem Dec.valAt_sub   : valAt (sub a b) e = valAt a e - valAt b e
theorem Dec.valAt_mul10 : valAt (mul10 a) e = 10 * valAt a e
theorem Dec.valAt_div10 : 10 * valAt (div10 a) e = valAt a e
theorem Dec.valAt_half  : 2 * valAt (half a) e = valAt a e
theorem Dec.valAt_rescale : valAt d e = valAt d f * 10^(f - e)
theorem Dec.cmp_spec    : cmp a b = sign (valAt a m - valAt b m)         -- m = min a.exp b.exp
```

That is, every arithmetic step of the formatter is exact and comparisons
decide the order of the represented values. Two length invariants of the
string builders are also proved (`errorChars_length`, `leadingSpaces_length`).

### Totality

Apart from the parser (`partial def`, backtracking recursive descent), the
evaluator (`partial def`, since Algol 68 programs need not terminate) and a
few fuel-bounded helpers, every definition is total: the lexer's main loop
recurses on the remaining input length with an explicit measure, the mode
equivalence check is fuel-bounded, and the formatting routines are structural
or use bounded loops. Lean's kernel accepts these definitions only with
termination arguments, so the corresponding non-termination bugs cannot occur.

## What is not proved

* The elaborator is not proved sound with respect to a formal semantics of
  Algol 68 (no such mechanised semantics exists); its behaviour is validated by
  differential testing against Algol 68 Genie (see [TESTING.md](TESTING.md)).
* `compile_correct` covers the compilation strategy for the integer expression
  core, not the full `Core` evaluator with names, rows, jumps and transput.
* The conversion from `Float` to `Dec` (`realToDec`) is a deliberate
  re-implementation of a68g's floating-point loop; it is tested (3,441
  differential cases), not proved, because its specification *is* a68g's
  behaviour.

## How to check

```bash
lake build            # elaborates all modules; any failing proof fails the build
```

The proofs use no axioms beyond Lean's standard three (`propext`,
`Classical.choice`, `Quot.sound`); no `sorry` appears anywhere in the code base
(`grep -rn sorry A68` is empty).
