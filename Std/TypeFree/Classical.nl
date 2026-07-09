---
# Type-Free Classical Logic
---
import Iff.
interpret True, False.
import DoubleNegation.

fix (∧) (∨) (∃).
assume or_iff_not_imp: P ∨ Q ⟺ (¬P ⟹ Q).
assume and_iff_nimp_not: P ∧ Q ⟺ ¬(P ⟹ ¬Q).
assume ex_iff_nall: (∃x. P.[x]) ⟺ ¬(∀x. ¬P.[x]).

begin

interpret Intuitionistic;
	goals.
	- for P Q if P: P, Q: Q then P ∧ Q;
		unfold and_iff_nimp_not;
		- if imp_not: P ⟹ ¬Q;


lemma and_iff_nor: P ∧ Q ⟺ ¬(¬P ∨ ¬Q);
