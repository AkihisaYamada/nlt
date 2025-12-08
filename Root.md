theory Root
- theory Base
- theory Classes
  * fix `∈`
  - theory Fun
    * fix `→`. assume `f ∈ A → B ⟹ x ∈ A ⟹ f x ∈ B`
- theory Prop
  * import Classes
  * fix `PROP`
  - theory Minimal
    * fix `false` `∧` `∨` `¬` `⟺`. assume ...
    * obtain `true` as `false ⟹ false`
  - theory Intuitionistic
    * import Minimal
    * assume `false ⟹ P ∈ PROP ⟹ P`
  - theory Classical
    * import Intuitionistic
    * assume `P ∈ PROP ⟹ P ∨ ¬P`
- theory FO
  * import Prop
  * fix `TYPE`
  - theory Choice
    * assume `(∃x ∈ A. P[x]) ⟹ A ∈ TYPE ⟹ (∀x. x ∈ A ⟹ P[x] ∈ PROP) ⟹ P[SOME x ∈ A. Y[x]]`
  - theory Minimal
    * import ..Minimal
    * fix `(∀∈)` `(∃∈)`.
  　  assume ball_elim: `∀x ∈ A. P[x] ⟹ A ∈ TYPE ⟹ (∀x. x ∈ A ⟹ P[x] ∈ PROP) ⟹ P[x]`
      assume ball_intro: `(∀x. x ∈ A ⟹ P[x]) ⟹ A ∈ TYPE ⟹ (∀x. x ∈ A ⟹ P[x] ∈ PROP) ⟹ ∀x ∈ A. P[x]`
  - theory Intuitionistic
    * import Minimal, ..Intuitionistic
  - theory Classical
    * import Intuitionistic, ..Classical
- theory HO
  * import FO, Fun
  * assume `A ∈ TYPE ⟹ B ∈ TYPE ⟹ A → B ∈ TYPE`
  - theory Minimal
    * import ..Minimal
  - theory Intuitionistic
    * import Minimal, ..Intuitionistic
  - theory Classical
    * import Intuitionistic, ..Classical
- theory Eq
  * fix `=`. assume `x = x`, `x = y ⟹ C[x] = C[y]`
  - theory Prop
    * import ..Prop
    - theory TwoValued
      * assume `(p ⟺ q) ⟹ p ∈ PROP ⟹ q ∈ PROP ⟹ p = q`
  - theory FO
    - import ..FO, Prop
    - fix `(∃!∈)`. assume `(∀x. x ∈ A ⟹ P[x] ∈ PROP) ⟹ (∃!x ∈ A. P[x]) ⟺ (∃x ∈ A. P[x]) ∧ (∀x ∈ A. ∀y ∈ A. P[x] ⟹ P[y] ⟹ x = y)`
    - theory UniqueChoice
      * assume `(∃!x ∈ A. Y[x]) ⟹ (∀x. x ∈ A ⟹ P[x] ∈ PROP) ⟹ Y[SOME x ∈ ι. Y[x]]`
    - theory Choice
      * import ..Choice
      * interpret UniqueChoice
  - theory HO
    * import FO, ..HO
    - theory Extensional
      * assume ext: `(∀x ∈ A. f x = g x) ⟹ f ∈ A → B ⟹ g ∈ A → B ⟹ f = g`
- theory TypeFree
  * fix `∧` `∨` `¬` `⟺`. assume ...
  - theory Intuitionistic
    * assume `false ⟹ P`
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

