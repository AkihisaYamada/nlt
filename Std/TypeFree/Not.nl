
---
# Negation

We consider negation as primitive, rather than as a derived notion of `false`.
This view allows to declare explosive `false` without exploding every contradiction `P ∧ ¬P`.
---

fix (¬).

begin

theory NotFalse :=
	assume not_false: ¬false.
end

theory NotIntro :=
	assume not_intro: if P ⟹ false then ¬P.
begin

	interpret NotFalse;
		by not_intro.

end

theory SelfRefutation :=
	assume imp_not_imp_not: if P ⟹ ¬P then ¬P.
begin

	interpret NotIntro;
		- if nP: P ⟹ false then ¬P;
			apply imp_not_imp_not;
			by #elim nP.
		.

end

theory MetaIrreflexive (⊏) :=
	assume irrefl: ¬ x ⊏ x.
end

theory MetaAsymmetric (⊏) :=
	assume asym: if x ⊏ y then ¬ y ⊏ x.
end
---
Note that antisymmetry is not yet definable, because it requires equality.
---


---
## Forward Contraposition

Here we consider one direction of contraposition `(P ⟹ Q) ⟹ ¬P ⟹ ¬Q`.
This assumption captures many of (somewhat surprising) behaviors of minimal logic,
most notably negative explosion: `¬P ⟹ P ⟹ ¬Q`.
---
theory ContraPos := -- @Latin modus tollens
	import not: MetaAntitone (¬) (⟹) (⟹).
begin

	lemma not_imp_imp_not: if nP: ¬P, QP: Q ⟹ P then ¬Q;
		by not.cmono[OF QP nP].

	lemma not_elim_not: if nP: ¬P, P: P then ¬Q;
		by not_imp_imp_not[OF nP] P.

	lemma nimp_intro: if P: P, nQ: ¬Q then ¬(P ⟹ Q);
		apply not_imp_imp_not[OF nQ];
		- if PQ: P ⟹ Q then Q;
			by PQ P.
		.
	lemma nimp_imp_imp: if imp: ¬(P ⟹ Q) ⟹ R then P ⟹ ¬Q ⟹ R;
		by imp nimp_intro.

	lemma nimp_elim2: if nimp: ¬(P ⟹ Q) then ¬Q;
		apply not_imp_imp_not[OF nimp].

	lemma nimp_not_elim1: if nimpn: ¬(P ⟹ ¬Q) then ¬ ¬ P;
		apply not_imp_imp_not[OF nimpn];
		- if nP, P;
			apply not_elim_not[OF nP P].
		.

	lemma nimp_not_elim: if nimp: ¬(P ⟹ ¬Q), imp: ¬ ¬ P ⟹ ¬ ¬ Q ⟹ R then R;
		apply imp;
		by nimp_elim2[OF nimp] nimp_not_elim1[OF nimp].

	lemma nall_intro1: for x if nPx: ¬ P.[x] then ¬(∀y. P.[y]);
		apply not_imp_imp_not[OF nPx].

	lemma nall_intro: if assm: ∀Q. (∀x. ¬ P.[x] ⟹ Q) ⟹ Q then ¬(∀y. P.[y]);
		apply assm;
		by #elim nall_intro1.

	lemma nnall_imp: if nnall: ¬ ¬ (∀x. P.[x]) then ∀x. ¬ ¬ P.[x];
		by not_imp_imp_not[OF nnall nall_intro1].

	lemma not_imp_not_true: if nP: ¬P, P: P then ¬true;
		by not_elim_not[OF nP P].

	lemma not_true_imp_not: if nt: ¬true then ¬P;
		apply not_elim_not[OF nt].

	lemma not_imp_not_false:
		if nP: ¬P then ¬false;
		apply not_imp_imp_not[OF nP].

	extend NotFalse begin

		interpret NotIntro;
			- if P0: P ⟹ false then ¬P;
				apply not.cmono[OF P0 not_false].
			.

	end

	theory MetaOrder (⊏) :=
		import MetaIrreflexive (⊏), MetaTransitive (⊏).
	begin
		interpret MetaAsymmetric (⊏);
			- for x y if xy: x ⊏ y then ¬ y ⊏ x;
				apply not_imp_imp_not[OF irrefl[of x]];
				- if yx: y ⊏ x then x ⊏ x;
					by trans[OF xy yx].
				.
			.
	end

	---
	Having explosive false yields `¬false ⟺ true`, but it does not make `¬true` explosive;
	`¬true` only implies `¬ ¬ false`.
	---
	lemma not_true_imp_nnot_false: if nt: ¬true then ¬ ¬ false;
		apply not_imp_imp_not[OF nt].

	extend MetaRelation begin

		extend AllRel begin

			lemma nall_intro1: for x if nPx: ¬ P.[x], xa: x ⊏ a then ¬(∀x ⊏ a. P.[x]);
				apply not_imp_imp_not[OF nPx];
				- if all: ∀x ⊏ a. P.[x];
					apply all_elim1[OF all xa].
				.
			lemma nall_intro: if assm: ∀Q. (∀x. ¬ P.[x] ⟹ x ⊏ a ⟹ Q) ⟹ Q then ¬(∀x ⊏ a. P.[x]);
				apply assm;
				- for x;
					by nall_intro1[of x].
				.

			lemma nnall_imp: if nnall: ¬ ¬ (∀x ⊏ a. P.[x]) then ∀x ⊏ a. ¬ ¬ P.[x];
				apply all_intro;
				- if xa: x ⊏ a;
					apply not_imp_imp_not[OF nnall];
					by nall_intro1[OF _ xa].
				.

		end

		extend ExRel begin

			lemma nex_elim1: if nex: ¬(∃x ⊏ a. P.[x]), xa: x ⊏ a then ¬ P.[x];
				by not.cmono[OF ex_intro1[OF _ xa] nex].

			lemma nex_elim: if nex: ¬(∃x ⊏ a. P.[x]), assm: (∀x. x ⊏ a ⟹ ¬ P.[x]) ⟹ Q then Q;
				apply assm;
				- for x;
					by nex_elim1[OF nex, of x].
				.

		end

	end

end

---
## "Minimal" Negation

We choose to specify minimal logic negation without mentioning `false`.
One merit of this formulation is that it becomes orthogonal to assuming `false` explosive or not.
---
theory NNotIntro :=
	assume nnot_intro:-- @English Double Negation Introduction
		if P then ¬ ¬P.
end

---
The following is a textbook formulation.
---
theory NotIntroContr :=
	assume not_intro_contr:-- @English negation introduction
		for Q if P ⟹ Q, P ⟹ ¬Q then ¬P.
end

---
We propose the following equivalent simpler version.
---
theory MinimalNot :=
	assume imp_not_sym: if P ⟹ ¬Q then Q ⟹ ¬P.
begin

	lemma not_intro_connect: if P: P, QnP: Q ⟹ ¬P then ¬Q;
		apply imp_not_sym[OF QnP P].

	interpret NNotIntro;
		- if P: P then ¬ ¬ P;
			apply not_intro_connect[OF P].
		.

	interpret ContraPos;
		- if PQ: P ⟹ Q, nQ: ¬Q then ¬P;
			apply not_intro_connect[OF nQ];
			by nnot_intro PQ.
		.

	theorem nnnot_elim: -- @English Triple Negation Elimination
		¬ ¬ ¬ P ⟹ ¬P;
		apply not.cmono[OF nnot_intro]>0.

	lemma not_intro_not_true: if imp: P ⟹ ¬true then ¬P;
		apply not_intro_connect[OF true_intro imp].

	interpret SelfRefutation;
		- if 1: P ⟹ ¬P then ¬P;
			apply not_intro_connect[OF 1];
			by nimp_intro nnot_intro.
		.
	interpret NotIntroContr;
		- for Q if PQ: P ⟹ Q, PnQ: P ⟹ ¬Q then ¬P;
			apply imp_not_imp_not;
			- if P;
				apply not_elim_not[of Q];
				by PQ PnQ P.
			.
		.

	-- `(¬ ¬ P ⟹ ¬Q) ⟺ (P ⟹ ¬Q)`
	lemma nnot_imp_imp: if imp: ¬ ¬ P ⟹ Q then P ⟹ Q;
		by imp nnot_intro.

	-- If the conclusion is negated, one can eliminate double negation.
	lemma nnot_elim_not: if nnP: ¬ ¬ P, PnQ: P ⟹ ¬Q then ¬Q;
		apply imp_not_sym[OF _ nnP];
		by nnot_intro imp_not_sym[OF PnQ].

	lemma nimp_not_intro: if nnP: ¬ ¬ P, nnQ: ¬ ¬ Q then ¬(P ⟹ ¬Q);
		apply nnot_elim_not[OF nnP];
		by nimp_intro nnQ.

	-- Double negated implication works as implication of double negation. 
	lemma nnimp_elim_nnot: if nnPQ: ¬ ¬ (P ⟹ Q), nnP: ¬ ¬ P then ¬ ¬ Q;
		apply nnot_elim_not[OF nnPQ];
		- if PQ;
			apply nnot_elim_not[OF nnP];
			by nnot_intro PQ.
		.

	extend MetaRelation begin

		extend ExRel begin

			lemma nex_intro: if all_not: ∀x. x ⊏ a ⟹ ¬ P.[x] then ¬(∃x ⊏ a. P.[x]);
				apply imp_not_imp_not;
				- if ex: ∃x ⊏ a. P.[x];
					apply ex_elim[OF ex];
					- for x if Px: P.[x], xa: x ⊏ a;
						by not_elim_not[OF all_not[OF xa] Px].
					.
				.
 
		end

	end

end

context NotIntroContr begin

	interpret? MinimalNot;
		interpret NNotIntro;
			- if P: P then ¬ ¬ P;
				by not_intro_contr[of P] P.
			.
		- if PnQ: P ⟹ ¬Q, Q then ¬P;
			apply not_intro_contr[OF PnQ];
			by nnot_intro Q.
		.

end

-- Under contraposition, minimal negation is equivalent to double negation introduction or self refutation.

context ContraPos begin

	extend NNotIntro begin

		interpret MinimalNot;
			- if PnQ: P ⟹ ¬Q, Q: Q then ¬P;
				apply not.cmono[OF PnQ];
				by nnot_intro[OF Q].
			.

	end

	extend SelfRefutation begin

		interpret NNotIntro;
			- if P: P then ¬ ¬P;
				apply imp_not_imp_not;
				- if nP: ¬P;
					by not_elim_not[OF nP P].
				.
			.
	end

end

---
Intuitionistic logic makes false explosive; in the false-free formulation, it means to
admit negation elimination `¬P ⟹ P ⟹ Q`.
---
theory ExplosiveNot :=
	assume not_elim: if ¬P, P then Q.
begin

	lemma not_true_elim: if 0: ¬true then Q;
		apply not_elim[OF 0].

	lemma not_elim_false: if nP: ¬P, P: P then false;
		apply not_elim[OF nP P].

end

theory IntuitionisticNot :=
	import NotIntro, ExplosiveNot.
begin

	interpret MinimalNot;
		- if PnQ: P ⟹ ¬Q, Q: Q then ¬P;
			by not_intro not_elim_false[OF _ Q] PnQ.
		.

end

theory ClaviusLaw :=
	assume not_imp_imp:
		-- @English Clavius's Law
		-- @Latin Consequentia Mirabilis
		if ¬P ⟹ P then P.

end

theory NNotElim :=
	assume nnot_elim:-- @English Double Negation Elimination
		if ¬ ¬ P then P.
end

---
Excluded middle allows case distinction.
---
theory ExcludedMiddle :=
	assume cases: if P ⟹ Q, ¬P ⟹ Q then Q.
begin

	interpret ClaviusLaw;
		- if nPP: ¬P ⟹ P then P;
			by cases[OF _ nPP].
		.

	interpret SelfRefutation;
		- if PnP: P ⟹ ¬P then ¬P;
			by cases[OF PnP].
		.

	lemma not_imp_elim: if nPQ: ¬P ⟹ Q, PR: P ⟹ R, QR: Q ⟹ R then R;
		apply cases[of P];
		- by PR.
		- by nPQ QR.
		.

end

---
Under Peirce's law, self-refutation principle, consequentia mirabilis and excluded middle coincide.
---
context SelfRefutation begin

	extend PeirceLaw begin

		interpret ExcludedMiddle;
			- if PQ: P ⟹ Q, nPQ: ¬P ⟹ Q then Q;
				apply peirce_law[of (¬P)];
				- if QnP: Q ⟹ ¬P then Q;
					apply nPQ;
					apply imp_not_imp_not;
					by QnP PQ.
				.
			.

	end

end

context ClaviusLaw begin

	extend PeirceLaw begin

		interpret ExcludedMiddle;
			- if PQ: P ⟹ Q, nPQ: ¬P ⟹ Q then Q;
				apply peirce_law[of P];
				- if QP: Q ⟹ P then Q;
					apply PQ;
					apply not_imp_imp;
					by nPQ QP.
				.
			.
	end

end


context ExplosiveNot begin
	---
	Clavius's law implies Pierce's law, and thus excluded middle.
	---
	extend ClaviusLaw begin

		interpret PeirceLaw;
			- for Q if PQP: (P ⟹ Q) ⟹ P then P;
				apply not_imp_imp;
				- if nP: ¬P;
					apply PQP;
					- if P: P then Q;
						by not_elim[OF nP P].
					.
				.
			.
		thm cases.

	end

end

---
Contraposition, non-inconsistency and explosiveness ends up in classical logic.
---
context ContraPos begin

	context NotFalse begin

		extend ExplosiveNot begin

			interpret ContraPos.SelfRefutation;
				- if PnP: P ⟹ ¬P then ¬P;
					apply not_intro;
					- if P: P then false;
						apply not_elim[OF PnP[OF P] P].
					.
				.
			interpret MinimalNot.

		end

	end

end

---
The following dual of minimal negation turns out to be "almost" classical,
in the sense that it is classical or nothing can be denied: `¬P` does not hold for any `P`.
---
theory CoMinimalNot :=
	assume not_imp_sym: if ¬P ⟹ Q then ¬Q ⟹ P.
begin

	lemma not_elim_connect: if nP: ¬P, nQP: ¬Q ⟹ P then Q;
		by not_imp_sym[OF nQP nP].

	interpret ExplosiveNot;
		- if nP: ¬P, P: P then Q;
			apply not_elim_connect[OF nP];
			by P.
		.

	interpret NNotElim;
		by not_imp_sym[OF imp.refl].

	interpret ContraPos;
		- if imp: P ⟹ Q, nQ: ¬Q then ¬P;
			apply not_elim_connect[OF nQ];
			by imp #elim nnot_elim.
		.

	lemma nnnot_intro: if not: ¬P then ¬ ¬ ¬P;
		apply not.cmono[OF nnot_elim not].

	extend NotFalse begin

		interpret ExplosiveNot.
		---
		Explosivity brings self refutation, which brings consequentia mirabilis, with which explosivity brings excluded middle.
		---
		interpret ClaviusLaw;
			- if imp: ¬P ⟹ P then P;
				apply nnot_elim;
				apply imp_not_imp_not;
				- if nP: ¬P;
					apply not.cmono[OF imp nP].
				.
			.
		thm cases.


	end

end

-- Co-minimal negation is equivalent to contraposition plus double-negation elimination.
context ContraPos begin

	extend NNotElim begin

		interpret CoMinimalNot;
			- if nPQ: ¬P ⟹ Q, nQ: ¬Q then P;
				apply nnot_elim;
				apply not.cmono[OF nPQ nQ].
			.

	end

end

---
The explosive negation is so strong that having any `P` and `¬P` collapses the
entire theory. One can consider the following weaker form.
---
theory ImplosiveNot :=
	assume nnot_not_imp: if ¬ ¬ P, ¬P then P.
begin

	extend ClaviusLaw begin
		interpret NNotElim;
			- if nnP: ¬ ¬ P then P;
				apply not_imp_imp;
				- if nP: ¬P;
					apply nnot_not_imp[OF nnP nP].
				.
			.
	end

end

context ExplosiveNot begin

	interpret ImplosiveNot;
		- if nnP: ¬ ¬ P, nP: ¬P then P;
			apply not_elim[OF nnP nP].
		.

end

theory InvContraPos :=
	import not: MetaInvAntitone (¬) (⟹) (⟹).
begin

	interpret ExplosiveNot;
		- if nP: ¬P, P: P then Q;
			apply not.inv_cmono[OF _ P];
			by nP.
		.

end


theory ClassicalNot :=
	import MinimalNot, NNotElim.
begin

	interpret CoMinimalNot.
	interpret NotFalse.-- This brings the excluded middle
	thm cases.

	interpret IntuitionisticNot.

	interpret InvContraPos;
		- if nPnQ: ¬P ⟹ ¬Q, Q: Q then P;
			apply not_imp_sym[OF nPnQ nnot_intro[OF Q]].
		.

	lemma nimp_elim1: if nimp: ¬(P ⟹ Q) then P;
		have nimp_nn: ¬(P ⟹ ¬ ¬ Q);
			apply not.cmono[OF _ nimp];
			apply imp.left_mono>1;
			apply nnot_elim>0.
		apply nimp_not_elim[OF nimp_nn];
		by #elim nnot_elim.

	lemma nimp_elim: if nimp: ¬(P ⟹ Q), assm: P ⟹ ¬Q ⟹ R then R;
		by assm nimp_elim1[OF nimp] nimp_elim2[OF nimp].

	lemma nall_elim:
		if nall: ¬(∀x. P.[x]), assm: ∀x. ¬ P.[x] ⟹ Q then Q;
		apply not_elim_connect[OF nall];
		- if nQ: ¬Q for x;
			apply not_imp_sym[OF assm];
			by nimp_intro nQ.
		.

	extend MetaRelation begin

		extend AllRel begin

			lemma nall_elim:
				if nall: ¬(∀x ⊏ a. P.[x]), assm: ∀x. ¬ P.[x] ⟹ x ⊏ a ⟹ Q then Q;
				apply not_elim_connect[OF nall];
				- if nQ: ¬Q;
					apply all_intro;
					- if xa: x ⊏ a then P.[x];
						apply not_imp_sym[OF assm];
						by nimp_intro xa nQ.
					.
				.
		end

	end

end
