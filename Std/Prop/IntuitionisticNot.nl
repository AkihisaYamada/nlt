
import Not, NotExplosive, ExplosiveNot.

begin

instance MinimalNot;
	- if PnQ: P ⟹ ¬Q, Q: Q, ... then ¬P;
		apply not_intro_inconsistent;
		- if P, ! R : Prop;
			apply not_elim[OF PnQ[OF P] Q].
		.
	.

extend ClaviusLaw begin

	instance PeirceLaw;
		- for Q if PQP: (P ⟶ Q) ⟶ P, ... then P;
			apply not_imp_imp;
			- if nP: ¬P;
				apply PQP[THEN imp_elim1], imp_intro;
				- if P: P then Q;
					by not_elim[OF nP P].
				.
			.
		.
	instance NNotElim;
		- if nnP: ¬ ¬ P, ... then P;
			apply not_imp_imp;
			by #elim not_elim[OF nnP].
		.

	instance ExcludedMiddle;
		- if PQ: P ⟹ Q, nPQ: ¬P ⟹ Q, ... then Q;
			apply peirce_law[of (¬P)], imp_intro;
			- if QnP: Q ⟶ ¬P then Q;
				apply nPQ;
				apply imp_not_imp_not;
				by QnP[THEN imp_elim1] PQ.
			.
		.

end
