theory Root
- theory Base
- theory Membership
  * interpret Base.
  * fix `∈`
  - theory Fun
    * fix `→`. assume `f ∈ A → B ⟹ x ∈ A ⟹ f x ∈ B`
- theory Prop
  * interpret Membership.
  * fix `PROP`
  - theory Eq
    * fix `(=)` `EQTYPE`
    * assume `A ∈ EQTYPE ⟹ a ∈ A ⟹ b ∈ A ⟹ (a = b) ∈ PROP`
    * assume `A ∈ EQTYPE ⟹ x = y ⟹ P[x] ⟹ x ∈ A ⟹ (∀z. z ∈ A ⟹ P[z] ∈ PROP) ⟹ P[y]`
  - theory Minimal
    * fix `false` `∧` `∨` `¬` `⟺`. assume ...
    * obtain `true` as `false ⟹ false`
  - theory Intuitionistic
    * import Minimal
    * assume `false ⟹ P ∈ PROP ⟹ P`
  - theory Classical
    * import Intuitionistic
    * assume `P ∈ PROP ⟹ P ∨ ¬P`
- theory FOL
  * import Prop
  * fix `TYPE` `(∀∈)` `(∃∈)`.
　  assume ball_elim: `∀x ∈ A. P[x] ⟹ A ∈ TYPE ⟹ (∀x. x ∈ A ⟹ P[x] ∈ PROP) ⟹ P[x]`
    assume ball_intro: `(∀x. x ∈ A ⟹ P[x]) ⟹ A ∈ TYPE ⟹ (∀x. x ∈ A ⟹ P[x] ∈ PROP) ⟹ ∀x ∈ A. P[x]`
  - theory ChoiceOp:
    * fix `SOME`.
      assume `A ∈ TYPE ⟹ (∀x. x ∈ A ⟹ P[x] ∈ PROP) ⟹ (SOME x ∈ A. P[x]) ∈ A`
      assume `(∃x ∈ A. P[x]) ⟹ A ∈ TYPE ⟹ (∀x. x ∈ A ⟹ P[x] ∈ PROP) ⟹ P[SOME x ∈ A. x]`
  - theory Eq:
    * import Prop.Eq.
    - theory Ex1
      * fix `(∃!)`
        assume `(∃!x ∈ A. P[x]) ⟹ A ∈ EQTYPE ⟹ (∀x. x ∈ A ⟹ P[x] ∈ PROP) ⟹ ∀Q. (∀x ∈ A. P[x] ⟹ (∀y ∈ A. P[y] ⟹ y = x) ⟹ Q) ⟹ Q`
        assume 
    - theory UniqueChoice
      * fix `(THE)`
        assume `A ∈ EQTYPE ⟹ (∀x. x ∈ A ⟹ P[x] ∈ PROP) ⟹ (THE x ∈ A. P[x]) ∈ A`
        assume `(∃!x ∈ A. P[x]) ⟹ A ∈ EQTYPE ⟹ (∀x. x ∈ A ⟹ P[x] ∈ PROP) ⟹ P[THE x ∈ A. P[x]]`
  - theory Minimal
    * import Prop.Minimal
  - theory Intuitionistic
    * import Minimal, Prop.Intuitionistic
  - theory Classical
    * import Intuitionistic, Prop.Classical
- theory HOL
  * import FOL, Fun.
  * assume `A ∈ TYPE ⟹ B ∈ TYPE ⟹ A → B ∈ TYPE`
  - theory Choice
    * assume `(∀x ∈ A. ∃y ∈ B. P x y) ⟹ A ∈ TYPE ⟹ B ∈ TYPE ⟹ ∃f ∈ A → B. P x (f x)`
  - theory Minimal
    * import FOL.Minimal
  - theory Intuitionistic
    * import Minimal, FOL.Intuitionistic
  - theory Classical
    * import Intuitionistic, FOL.Classical
- theory Eq
  * fix `=`. assume `x = x`, `x = y ⟹ C[x] = C[y]`
  - theory Prop
    * import Root.Prop
    - theory TwoValued
      * assume `P ⟹ Q ⟹ P ∈ PROP ⟹ Q ∈ PROP ⟹ P = Q`
        assume `P ⟹ P ∈ PROP ⟹ Q ∈ PROP ⟹ (P ⟹ Q) = Q`
  - theory FOL
    - import Root.FOL, Prop
    - fix `(∃!∈)`. assume `(∀x. x ∈ A ⟹ P[x] ∈ PROP) ⟹ (∃!x ∈ A. P[x]) ⟺ (∃x ∈ A. P[x]) ∧ (∀x ∈ A. ∀y ∈ A. P[x] ⟹ P[y] ⟹ x = y)`
    - theory UniqueChoice
      * assume `(∃!x ∈ A. Y[x]) ⟹ A ∈ TYPE ⟹ (∀x. x ∈ A ⟹ P[x] ∈ PROP) ⟹ Y[SOME x ∈ ι. Y[x]]`
    - theory Choice
      * import Root.FOL.Choice
      * interpret UniqueChoice
  - theory HOL
    * import FOL, Root.HOL
    - theory Extensional
      * assume ext: `(∀x ∈ A. f x = g x) ⟹ A ∈ TYPE ⟹ B ∈ TYPE ⟹ f ∈ A → B ⟹ g ∈ A → B ⟹ f = g`
- theory TypeFree:
  - theory Minimal:
    * fix `∧` `∨` `¬` `⟺`. assume ...
  - theory Intuitionistic:
    * import Minimal.
    * assume `false ⟹ P`.
- theory Lambda
  * import Eq
  * fix `λ`. assume `(λx. C[x]) y = C[y]`
  - theory Nat
    * fix `nat` `0` `Suc`.
  - theory Logic
    - define `x ∧ y := ∀P. x ⟹ y ⟹ P`
    - define `x ∨ y := ∀P. (x ⟹ P) ⟹ (y ⟹ P) ⟹ P`
    - interpret decided: Prop.Classical
    - interpret TypeFree.Intuitionistic
    * theory Nat
      - import ..Nat
      - interpret HeytingArith
- theory HeytingArith
  * import FO.Intuitionistic
  * import Lambda
  * import Nat
- theory PeanoArith
  * import FO.Classical
  * import Lambda
  * import Nat
  * interpret HeytingArith

