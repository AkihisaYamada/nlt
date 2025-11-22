theory Root
- theory Prop
  * fix `:` `prop` `∧` `∨` `¬` `⟺`. assume ...
  * theory Intuitionistic
    - assume `false ⟹ P : prop ⟹ P`
  * theory Classical
    - import Intuitionistic
    - assume `P : prop ⟹ P ∨ ¬P`
- theory Fun
  * fix →. assume `f : ι → τ ⟹ x : ι ⟹ f x : τ`
- theory FO
  * import Prop
  * fix `(∀:)` `(∃:)`. assume...
  * theory Choice
    - assume `(∃x:ι. P[x]) ⟹ (∀x. x : ι ⟹ P[x] : prop) ⟹ P[SOME x:ι. Y[x]]`
  - theory Intuitionistic
    * import Prop.Intuitionistic
  - theory Classical
    * import Intuitionistic, Prop.Classical
- theory HO
  * import FO, Fun
  * theory Intuitionistic
    - import FO.Intuitionistic
  * theory Classical
    - import Intuitionistic, FO.Classical
- theory Eq
  * fix `=`. assume `x = x`, `x = y ⟹ C[x] = C[y]`
  * theory Prop
    - import Root.Prop
    - theory TwoValued
      * assume `(p ⟺ q) ⟹ p : prop ⟹ q : prop ⟹ p = q`
  * theory FO
    - import Root.FO
    - import Prop
    - fix `(∃!:)`. assume `(∀x. x : ι ⟹ P[x] : prop) ⟹ (∃!x:ι. P[x]) ⟺ (∃x:ι. P[x]) ∧ (∀x:ι. ∀y:ι. P[x] ⟹ P[y] ⟹ x = y)`
    - theory UniqueChoice
      * assume `(∃!x:ι. Y[x]) ⟹ (∀x. x : ι ⟹ P[x] : prop) ⟹ Y[SOME x:ι. Y[x]]`
    - theory Choice
      * import FO.Choice
      * interpret UniqueChoice
  * theory HO
    - import Prop
    - import Root.HO
    - theory Extensional
      * assume ext: `(∀x:ι. f x = g x) ⟹ f : ι → τ ⟹ g : ι → τ ⟹ f = g`
- theory TypeFree
  * fix `∧` `∨` `¬` `⟺`. assume ...
  * theory Intuitionistic
    - assume `false ⟹ P`
- theory Lambda
  * import Eq
  * fix `λ`. assume `(λx. C[x]) y = C[y]`
  * theory Nat
    - fix `nat` `0` `Suc`.
  * theory Logic
    - define `x ∧ y := ∀P. x ⟹ y ⟹ P`
    - define `x ∨ y := ∀P. (x ⟹ P) ⟹ (y ⟹ P) ⟹ P`
    - interpret decided: Prop.Classical
    - interpret TypeFree.Intuitionistic
    - theory Nat
      * import Lambda.Nat
      * interpret HeytingArith
- theory HeytingArith
  * import FO.Intuitionistic
  * import Lambda
  * import Nat
- theory PeanoArith
  * import FO.Classical
  * import Lambda
  * import Nat
  * interpret HeytingArith

