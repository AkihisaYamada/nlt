import base? TypeFree.Not.

begin

extend base? ContraPos begin

	lemma not_cong#cong if PQ: P ⟺ Q then ¬ P ⟺ ¬ Q;
		apply+ iff_intro not.cmono>1;
		unfold PQ.

end

extend base? MinimalNot begin

	interpret .ContraPos.

	lemma not_iff_imp_not: if P: P then ¬Q ⟺ (Q ⟹ ¬P);
		apply iff_intro;
		- by #elim not_elim_not.
		- if QnP; apply imp_not_imp_not;
			by P #elim QnP not_elim_not.
		.
	lemma imp_not_commute: (P ⟹ ¬Q) ⟺ (Q ⟹ ¬P);
		apply iff_intro[OF imp_not_sym imp_not_sym].

	lemma nnnot_iff: ¬ ¬ ¬ P ⟺ ¬ P;
		apply iff_intro[OF nnnot_elim nnot_intro].

	lemma nnot_imp_not_iff: (¬ ¬ P ⟹ ¬Q) ⟺ (P ⟹ ¬Q);
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

	extend Iff.AllRel begin

		interpret base.AllRel.

		lemma nnall_not_iff: ¬ ¬ (∀x ⊏ a. ¬ P.[x]) ⟺ (∀x ⊏ a. ¬ P.[x]);
			apply iff_intro;
			- if nnall;
				use nnall_imp[OF nnall];
				note#cong all_cong_weak.
				unfold nnnot_iff.
			by nnot_intro.

	end

	extend Iff.ExRel begin

		interpret base.ExRel.

		lemma nex_nnot: ¬(∃x ⊏ a. ¬ ¬ P.[x]) ⟺ ¬(∃x ⊏ a. P.[x]);
			by iff_intro nex_intro #elim nex_elim #simp nnnot_iff.

	end

end

extend base? ClassicalNot begin

	interpret .MinimalNot.

	lemma nnot_iff#simp ¬ ¬ P ⟺ P;
		apply iff_intro[OF nnot_elim nnot_intro].

	lemma nimp_iff_all: ¬(P ⟹ Q) ⟺ (∀R. (P ⟹ ¬Q ⟹ R) ⟹ R);
		apply iff_intro;
		- by #elim nimp_elim.
		- if all;
			apply all;
			by nimp_intro.
		.

	lemma not_imp_iff_all: (¬P ⟹ Q) ⟺ (∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R);
		apply iff_intro;
		- by #elim not_imp_elim.
		- if all;
			apply all;
			by #elim not_elim.
		.

	lemma nall_iff_all: ¬(∀x. P.[x]) ⟺ (∀Q. (∀x. ¬ P.[x] ⟹ Q) ⟹ Q);
		apply iff_intro[OF _ nall_intro];
		- if nall for Q if assm;
			apply nall_elim[OF nall];
			apply assm=.
		.

	extend AllRel begin

		interpret base.AllRel.

	end

end
