base Root;

import PredicateLogic;

assume ex_defined: (∀x. defined α.[x]) ⟹ defined (∃x. α.[x]);

setup rewrite iff.refl iff.sym iff.trans iff_elim1;
setup cong
	P ⟹ Q: iff_cong_imp,
	P ⟺ Q: iff_cong_iff,
	P ∧ Q: iff_cong_and,
	P ∨ Q: iff_cong_or,
	¬P: iff_cong_not,
	defined P: iff_cong_defined,
	!(∀x. α.[x]): iff_cong_all,
	!(∃x. α.[x]): iff_cong_ex;

setup conclude imp.refl iff.refl true_intro;

show all_defined: if arg: ∀x. defined α.[x] then defined (∀x. α.[x]);
	show nna: ¬¬α.[x] ⟺ α.[x];
		unfold nnot_iff[OF arg];
		by iff.refl;
	fold nna;
	fold nex_iff_all_not;
	apply+ not_defined ex_defined;
	case for x;
		apply not_defined;
		by arg;
	qed;

show nall_iff_ex_not: if arg: ∀x. defined α.[x] then ¬(∀x. α.[x]) ⟺ (∃x. ¬α.[x]);
	apply iff_intro;
	case nall: ¬(∀x. α.[x]);
		show exd: defined (∃x. ¬α.[x]);
			apply ex_defined;
			by all_all_imp(x. defined α.[x])(x. defined (¬α.[x]))[OF arg not_defined];
		apply defined_elim[OF exd];
		case exn: ∃x. ¬α.[x];
			by exn;
		case nexn: ¬(∃x. ¬α.[x]);
			show allnn: ∀x. ¬¬α.[x];
				by nexn[unfolded nex_iff_all_not];
			show all: α.[x];
				by allnn[unfolded nnot_iff[OF arg]];
			by not_elim[OF nall all];
		qed;
	case exn: ∃x. ¬α.[x];
		by ex_not_imp_nall[OF exn];
	qed;

