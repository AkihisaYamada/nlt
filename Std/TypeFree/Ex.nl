---
## Type-Free Existence
---
fix (∃).
assume ex_intro1: for x if P.[x] then ∃x. P.[x].
assume ex_elim: if ∃x. P.[x], ∀x. P.[x] ⟹ Q then Q.

begin

lemma ex_intro: if assm: ∀Q. (∀x. P.[x] ⟹ Q) ⟹ Q then ∃x. P.[x];
	apply assm;
	- for x;
		by ex_intro1[of x].
	.

