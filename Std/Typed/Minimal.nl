---
## Propositional Minimal Logic
---
import True, And, Or, Not, MinimalNot, Iff.

begin

lemma not_cong#cong if PQ: P ⟺ Q, [P : Prop, Q : Prop] then ¬ P ⟺ ¬ Q;
	by iff_intro #elim not_imp_imp_not #simp PQ.
