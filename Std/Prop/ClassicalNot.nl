import MinimalNot.
assume nnot_elim: if ¬ ¬ P, P : Prop then P.

begin

lemma not_elim_connect: if nQ: ¬Q, imp: ¬P ⟹ Q, [P : Prop, Q : Prop] then P;
	apply nnot_elim;
	apply imp_not_imp_not;
	- if nP: ¬P;
		apply not_elim_not[OF nQ];
		by imp nP.
	.

instance IntuitionisticNot;
	- for P if nP: ¬P, ... for Q if ...;
		apply not_elim_connect[OF nP].
	.

instance ClaviusLaw;
	- if imp: ¬P ⟹ P, ... then P;
		apply nnot_elim;
		apply imp_not_imp_not;
		- if nP: ¬P, ...;
			apply not.cmono[OF imp]; by nP.
		.
	.

lemma nimp_elim1: if nimp: ¬(P ⟶ Q), [P : Prop, Q : Prop] then P;
	have nimp_nn: ¬(P ⟶ ¬ ¬ Q);
		apply not_imp_imp_not[OF nimp];
		apply imp_IMP.left_mono>4;
		by #elim nnot_elim.
	apply nimp_not_elim[OF nimp_nn];
	by #elim nnot_elim.

lemma nimp_elim: if nimp: ¬(P ⟶ Q), assm: P ⟹ ¬Q ⟹ R, [P : Prop, Q : Prop] then R;
	by assm nimp_elim1[OF nimp] nimp_elim2[OF nimp].
