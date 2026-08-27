# Naive Logic Tool

This is a proof assistant based on a naive foundation of logic.

## Install

To build, please install `make` and `g++`, and run `make`. It will produce `nlt`.

## Basic Usage

An invocation of `nlt` creates an initial *theory* with no axioms and symbols, except for `∀` and `⟹`
provided by the naive foundation.
Typically, users start by importing library theories for the logic they want to use, e.g.,
```
> import Std, Eq, Prop, Nat.
```
where the left-most `>` symbols are prompt from the tool and not to be included in user inputs.
The main development of a theory should start with
```
> begin
```
which indicates that axiomatization is finished.

### Proving Theorems

A theorem statement would look like:
```
> theorem 2_mul_nat_eq: if x_is_nat: x : ℕ then 2 * x = x + x;
```
The theorem is named `2_mul_nat_eq`, and the statement is naturally: if `x : ℕ` then `2 * x = x + x`,
and formally `∀x. x : ℕ ⟹ 2 * x = x + x`.
The assumption `x : ℕ` is referred to by name `x_is_nat` in the proof.

Only the following two constructions have special meaning to `nlt` kernel:

- `∀x. t`, meaning that `t` holds, where `x` is instantiated to an arbitrary (closed) term;
- `s ⟹ t` means if `s` holds, then `t` holds.

Importantly, `:` or `=` have no special meaning for the kernel.

Let's prove `2_mul_nat_eq`, by induction on `x`. The induction principle on `ℕ` is named `nat_induction`
and can be printed by:
```
>> thm nat_induction.
```
which will show the following fact (modulo indentation):
```
∀ x P. P.[0] ⟹
       (∀ x. P.[x] ⟹ x : ℕ ⟹ P.[suc x]) ⟹
       (∀ x. x : ℕ ⟹ P.[x] : Prop) ⟹
       x : ℕ ⟹ P.[x]
```
Here, `P.[s]` means that `P` should be instantiated to a term of form `x. t` and represents `t` where
the extra variable `x` is replaced by `s`.
We proceed the proof by:
```
>>  apply nat_induction[of x];
```
Here, `[of x]` indicates that the first variable of `nat_induction` (which is called `x`) is instantiated to `x`,
which is fixed by the claim `2_mul_nat_eq`. Then `nlt` will figure out that `P` should be instantiated to
`x'. 2 * x' = x' + x'` and asks you to prove corresponding instances of the four premises of `nat_induction`:
```
  applied goals:
        1. 2 * 0 = 0 + 0
        2. ∀ x'. 2 * x' = x' + x' ⟹ x' : ℕ ⟹ 2 * suc x' = suc x' + suc x'
        3. ∀ x'. x' : ℕ ⟹ 2 * x' = x' + x' : Prop
        4. x : ℕ
```
Canonically, there should be four subproofs, each started by `-` and ended by `.`. The first one is automatic:
```
>>  - .
```
The second one needs a bit of manual proving. A canonical subproof statement should look like
```
>>  - for y if IH: 2 * y = y + y, y_is_nat: y : ℕ then 2 * suc y = suc y + suc y;
```
Here, `for y` declares that you will prove the goal of form `∀x'. P.[x']` by proving `P.[y]` for fresh `y`.
The `if` part is giving names to the two assumptions. There are some short forms, for instance:
```
>>  - for y if IH, y_is_nat;
```
or
```
>>  - if IH: 2 * y = y + y, y_is_nat;
```
have the same meaning.
Now looking at the left-hand side `2 * suc y` of the goal, you would like to simplify it by `mul_suc`:
```
  ∀ x. x : ℕ ⟹ ∀ y. y : ℕ ⟹ x * suc y = x + x * y
```
To this to succeed, the instances `2 : ℕ` and `y : ℕ` of the premises must be known to `nlt`.
While the former is already known, for the latter you have to declare `y_is_nat` as such a knowledge.
You can do so by command:
```
>>> note! y_is_nat.
```
or declare already at the goal statement:
```
>>  - for y if IH: 2 * y = y + y, y_is_nat! y : ℕ then 2 * suc y = suc y + suc y;
```
or shorter:
```
>>  - if IH: 2 * y = y + y, ...;
```
Now you can unfold the goal by `mul_suc`:
```
>>> unfold mul_suc;
    unfolded goals:
        1. 2 + 2 * y = suc y + suc y
```
Here you see the left-hand side of the `IH: 2 * y = y + y`, so you can proceed by:
```
>>> unfold IH;
    unfolded goals:
        1. 2 + (y + y) = suc y + suc y
```
This goal is now automatic and you can conclude the subgoal by `.`. You can also shorten the
proof by telling `nlt` which facts should be used as *simplification rules*, e.g.:
```
>>  - if IH: 2 * y = y + y, ...; by #simp IH.
```
You don't have to name `mul_suc`, which is actually already declared as `#simp`.

A type-dependent user might not recognize that there are remaining subgoals:
```
        3. ∀ x'. x' : ℕ ⟹ 2 * x' = x' + x' : Prop
        4. x : ℕ
```
The third one is provable thanks to `nat_eq_prop`:
```
∀ x. x : ℕ ⟹ ∀ y. y : ℕ ⟹ x = y : Prop
```
and the last one is the assumption `x_is_nat` of our main claim. You can complete the proof by
```
>>  - by nat_eq_prop.
>>  - by x_is_nat.
>>  .
```

## Obtaining Constants

If your foundation admits equality `=` (or any reflexive relation), then
```
> definition c = body.
```
is available. Internally, it corresponds to more general `obtain` command:
```
obtain c where c_def: c = body;
  - for thesis if assm: ∀c. c = body ⟹ thesis then thesis;
    by assm[of body].
  .
```
It is sometimes better to use `obtain` and specify only essential properties,
since other theories can *replace* the constant by a term that satisfies the properies. 
