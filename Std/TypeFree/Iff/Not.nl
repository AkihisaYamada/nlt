import TypeFree.Not.

begin

extend ContraPos begin

	lemma not_cong#cong if PQ: P ⟺ Q then ¬ P ⟺ ¬ Q;
		apply+ iff_intro not.cmono>1;
		unfold PQ.

end

extend MinimalNot begin

	interpret .ContraPos.

	lemma not_iff_imp_not_true: ¬P ⟺ (P ⟹ ¬true);
		apply iff_intro[OF _ imp_not_true_imp_not];
		by #elim not_elim_not.

	lemma imp_not_commute: (P ⟹ ¬Q) ⟺ (Q ⟹ ¬P);
		apply iff_intro[OF imp_not_sym imp_not_sym].

	lemma nnnot_iff: ¬ ¬ ¬ P ⟺ ¬ P;
		apply iff_intro[OF nnnot_elim nnot_intro].

	lemma nnot_imp_iff: (¬ ¬ P ⟹ ¬Q) ⟺ (P ⟹ ¬Q);
		unfold imp_not_commute;
		simp nnnot_iff.

	lemma nnimp_not_iff: ¬ ¬ (P ⟹ ¬Q) ⟺ (P ⟹ ¬Q);
		apply iff_intro[OF _ nnot_intro];
		- if nnPnQ: ¬ ¬ (P ⟹ ¬Q), P: P;
			apply nnot_elim_not[OF nnPnQ];
			- if PnQ;
				by PnQ P.
			.
		.

	lemma not_nniff_not: ¬ ¬ (¬ P ⟺ ¬ Q) ⟺ (¬ P ⟺ ¬ Q);
		apply iff_intro[OF _ nnot_intro];
		- if nniff;
			apply iff_intro;
			- if nP;
				apply nnot_elim_not[OF nniff];
				- if iff;
					by nP[unfold iff].
				.
			- if nQ;
				apply nnot_elim_not[OF nniff];
				- if iff;
					by nQ[fold iff].
				.
			.
		.

	lemma nnall_not_iff: ¬ ¬ (∀x. ¬ P.[x]) ⟺ (∀x. ¬ P.[x]);
		apply iff_intro;
		- if nnall;
			use nnall_imp[OF nnall];
			unfold nnnot_iff.
		by nnot_intro.

end

extend ClassicalNot begin

	interpret .MinimalNot.

	lemma nnot_iff#simp ¬ ¬ P ⟺ P;
		apply iff_intro[OF nnot_elim nnot_intro].

end	
