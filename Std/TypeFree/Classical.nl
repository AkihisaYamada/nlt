---
# Type-Free Classical Logic
---
import Iff.

import Not, ClassicalNot.

fix (∧) (∨) (∃).
assume or_iff_imp: P ∨ Q ⟺ (¬P ⟹ Q).
assume and_iff_nimp: P ∧ Q ⟺ ¬(P ⟹ ¬Q).
assume ex_iff_nall: (∃x. P.[x]) ⟺ ¬(∀x. ¬P.[x]).

begin

interpret Intuitionistic;
	- show: P ∧ Q ⟺ (∀R. (P ⟹ Q ⟹ R) ⟹ R);
		simp and_iff_nimp nimp_iff_all.
	- show: P ∨ Q ⟺ (∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R);
		simp or_iff_imp not_imp_iff_all.
	- show: (∃ x. P.[x]) ⟺ (∀ Q. (∀ x. P.[x] ⟹ Q) ⟹ Q);
		simp ex_iff_nall nall_iff_all.
	.

