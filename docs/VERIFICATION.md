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

### The optimisation passes (`A68/Verified/Opt.lean`)

The passes of `A68.Opt` are stated over the same formal core and proved to
preserve meaning:

```lean
theorem opt_correct (e : Expr) (env : List Int) : (Expr.opt e).eval env = e.eval env
theorem opt_size    (e : Expr) : (Expr.opt e).size ≤ e.size
theorem opt_idempotent (e : Expr) : Expr.opt (Expr.opt e) = Expr.opt e
```

and composed with compiler correctness into an end-to-end statement — the code
generated for the *optimised* program computes what the *source* program
denotes:

```lean
theorem opt_compile_correct (e : Expr) (st env : List Int) :
    exec (compile (Expr.opt e)) ⟨st, env⟩ = ⟨e.eval env :: st, env⟩
```

The rules modelled are exactly the ones the production pass applies, and the
model is deliberately as conservative: an operator is folded only when *all* its
operands are literals, because in the real language an operand may have side
effects or may fail. Algebraic identities that would drop an operand (`x * 0`)
are not applied by either.

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

### The multi-precision kernel (`A68/Verified/MP.lean`)

`LONG` and `LONG LONG` arithmetic (`A68.MP`) is a step-by-step re-implementation of
a68g's `mp.c`, rounding quirks included, so its specification is a68g's behaviour
and it is checked by differential testing. What is proved is that the steps a68g
relies on to be *exact* are exact. With `digVal a n` the integer that positions
`0 … n` of a digit array denote in radix `R = 10⁷`:

```lean
theorem carryAt_digVal    : digVal (carryAt a j) n = digVal a n          -- 1 ≤ j ≤ n, j < a.size
theorem normFrom_digVal   : digVal (normFrom a k j) n = digVal a n       -- j ≤ n, j < a.size
theorem normDigits_digVal : digVal (normDigits w k digs) digs = digVal w digs
theorem dblOfInt_exact    : n.natAbs < 2 ^ 53 → dblOfInt n = n
theorem fma_exact         : (a * b + c).natAbs < 2 ^ 53 → fma a b c = a * b + c
theorem dv_linear         : dv (fun i => f i + s * g i) n = dv f n + s * dv g n
theorem alignedSum_digit  : -- scratch digit i of add_mp / sub_mp = x digit + s · y digit, aligned
theorem alignedSum_equal_exponents :
    digVal (alignedSum x y e e digs s).1 (digs + 2) = R * (dv x digs + s * dv y digs)
theorem toDecParts_mant, mantOf_succ, R_eq : R = 10 ^ logR
```

That is: `norm_mp`'s carry propagation never changes the number being normalised;
a68g's double arithmetic on scratch digits (which stay below 2⁵³) is exact, so it
can be modelled with integers, and the only inexact double computation — the
quotient-digit estimate of the division routines, which clang fused into `fmadd` —
is modelled by `dblOfInt`/`fma`/`truncDiv`, which round exactly as IEEE does;
the scratch number that addition and subtraction normalise and round is the exact
sum of the aligned operands; and decimal output starts from a mantissa that is the
digit value itself, with one radix digit equal to seven decimal digits. The rounding
that follows (`round_internal_mp`) is deliberately not "proved correct": it is
a68g's, including its unusual half-way rule, and is tested instead.

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
* `compile_correct` and `opt_compile_correct` cover the compilation strategy for
  the integer expression core, not the full `Core` with names, rows, jumps and
  transput. The production optimiser applies the proved rewrites plus two whose
  models are not stated here: the frameless-block flattening with its de Bruijn
  depth shift, and the `deref (refCell …)` peephole.
* **The C emission is not proved.** `A68.CodeGen` produces C text, and the
  system C compiler turns it into machine code; verifying that layer would be a
  CompCert-scale project. It is validated the same way the rest is: every
  corpus program and every fuzz case is compiled and its bytes compared with
  a68g's, and with the interpreter's, which shares the runtime with it.
  What the proofs do cover is the *strategy* the emitter follows — the operand
  stack discipline of `A68.Verified.StackMachine`.
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
