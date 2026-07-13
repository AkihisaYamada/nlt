import TypeFree.Not.

begin

extend ContraPos begin

	lemma not_cong#cong if PQ: P ⟺ Q then ¬ P ⟺ ¬ Q;
		apply+ iff_intro not.cmono>1;
		unfold PQ.

end

extend MinimalNot begin

	lemma nnnot_iff: ¬ ¬ ¬ P ⟺ ¬ P;
		apply iff_intro[OF nnnot_elim nnot_intro].

	lemma nnall_not_iff: ¬ ¬ (∀x. ¬ P.[x]) ⟺ (∀x. ¬ P.[x]);
		apply iff_intro;
		- if nnall;
			use nnall_imp[OF nnall];
			unfold nnnot_iff.
		by nnot_intro.

end

extend CoMinimalNot begin

	lemma nnnot_iff: ¬ ¬ ¬ P ⟺ ¬ P;
		apply iff_intro[OF nnot_elim nnnot_intro].

	lemma nnall_not_iff: ¬ ¬ (∀x. P.[x]) ⟺ (∀x. P.[x]);
		apply iff_intro[OF nnot_elim];
	
