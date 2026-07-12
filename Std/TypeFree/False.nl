---
## Explosive False 

We can obtain `false` via `∀P. P` to satisfy the law of explosion.
---

obtain false where false_elim#elim
	-- @English Law of Explosion
	-- @Latin ex falso quodlibet
	if false then P;
	- for thesis if assm;
		by assm[of (∀P. P)].
	.
interpret imp: MetaLeftBound (⟹) false.

extend Iff begin

	lemma false_imp_iff#simp (false ⟹ P) ⟺ true;
		by iff_true.

end

extend FalseNot begin

	lemma not_elim: if nP: ¬P, P: P then Q;
		use not_imp_false[OF nP P].

	extend Iff begin

		lemma not_imp_iff_false: if nP: ¬P then P ⟺ false;
			by iff_intro not_imp_false[OF nP].

	end

end
