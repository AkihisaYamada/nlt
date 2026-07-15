
---
# Negation

We consider negation as primitive, rather than as a derived notion of `false`.
This view allows to declare explosive `false` without exploding every contradiction `P ∧ ¬P`.
---

fix (¬).

begin

theory NotInconsistent :=
	assume not_inconsistent: ¬(∀P. P).
end

theory NotIntro :=
	assume not_intro: if P ⟹ ∀Q. Q then ¬P.
begin

	interpret NotInconsistent;
		by not_intro.

	extend False begin

		lemma not_false: ¬false;
			by not_intro.

	end

end

theory SelfRefutation :=
	assume self_refutation: if P ⟹ ¬P then ¬P.
begin

	interpret NotIntro;
		- if nP: P ⟹ ∀Q. Q then ¬P;
			apply self_refutation;
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
theory ContraPos :=
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

	lemma nimp_imp_not: if nimp: ¬(P ⟹ Q) then ¬Q;
		apply not_imp_imp_not[OF nimp].

	lemma nimp_not_imp_nnot: if nimpn: ¬(P ⟹ ¬Q) then ¬ ¬ P;
		apply not_imp_imp_not[OF nimpn];
		- if nP, P;
			apply not_elim_not[OF nP P].
		.
	lemma nimp_not_elim_nnot: if nimp: ¬(P ⟹ ¬Q), imp: ¬ ¬ P ⟹ ¬ ¬ Q ⟹ R then R;
		apply imp;
		by nimp_imp_not[OF nimp] nimp_not_imp_nnot[OF nimp].

	lemma not_imp_not_all: if nPx: ¬ P.[x] then ¬(∀y. P.[y]);
		apply not_imp_imp_not[OF nPx].

	lemma nnall_imp: if nnall: ¬ ¬ (∀x. P.[x]) then ∀x. ¬ ¬ P.[x];
		by not_imp_imp_not[OF nnall not_imp_not_all].

	lemma not_imp_not_true: if nP: ¬P, P: P then ¬true;
		by not_elim_not[OF nP P].

	lemma not_true_imp_not: if nt: ¬true then ¬P;
		apply not_elim_not[OF nt].

	lemma not_imp_not_inconsistent:
		if nP: ¬P then ¬(∀Q. Q);
		apply not_imp_imp_not[OF nP].

	extend NotInconsistent begin

		interpret NotIntro;
			- if P0: P ⟹ ∀Q. Q then ¬P;
				apply not.cmono[OF P0 not_inconsistent].
			.

	end

	theory MetaOrder :=
		import MetaIrreflexive.
		import MetaTransitive.
	begin
		interpret MetaAsymmetric;
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
	lemma not_true_imp_nnot_false: if nt: ¬true then ¬ ¬ Q;
		apply not_imp_imp_not[OF nt].


end

---
## "Minimal" Negation

Traditional minimal logic with false "define"s negation by `¬P ⟺ (P ⟹ ⊥)` for free `⊥`.
We can formulate the equivalent without mentioning `⊥`, which corresponds to `¬true`,
as follows.
It is also equivalent to forward contraposition with double-negation introduction.
---
theory NNotIntro :=
	assume nnot_intro:-- @English Double Negation Introduction
		if P then ¬ ¬P.
end

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

	lemma imp_not_true_imp_not: if imp: P ⟹ ¬true then ¬P;
		apply not_intro_connect[OF true_intro imp].

	interpret SelfRefutation;
		- if 1: P ⟹ ¬P then ¬P;
			apply not_intro_connect[OF 1];
			by nimp_intro nnot_intro.
		.

	-- `(¬ ¬ P ⟹ ¬Q) ⟺ (P ⟹ ¬Q)`
	lemma nnot_imp_imp: if imp: ¬ ¬ P ⟹ Q then P ⟹ Q;
		by imp nnot_intro.

	lemma imp_not_nnot_imp_not: if PnQ: P ⟹ ¬Q then ¬ ¬ P ⟹ ¬Q;
		apply imp_not_sym>1;
		by nnot_intro imp_not_sym[OF PnQ].

	lemma nnot_elim_not: if nnP: ¬ ¬ P, PnQ: P ⟹ ¬Q then ¬Q;
		apply self_refutation;
		- if Q;
			have nP: ¬P;
				use imp_not_sym[OF PnQ Q].
			by not_elim_not[OF nnP nP].
		.

	lemma nnimp_imp_nnot: if nnPQ: ¬ ¬ (P ⟹ Q), P: P then ¬ ¬ Q;
		apply not_intro_connect[OF nnPQ];
		- if nQ: ¬Q then ¬ ¬ ¬ (P ⟹ Q);
			apply nnot_intro;
			apply nimp_intro[OF P nQ].
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
				apply self_refutation;
				- if nP: ¬P;
					by not_elim_not[OF nP P].
				.
			.
	end

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
Intuitionistic logic makes false explosive; in the false-free formulation, admits
negation elimination `¬P ⟹ P ⟹ Q`.
---
theory ExplosiveNot :=
	assume not_elim: if ¬P, P then Q.
begin

	lemma not_true_elim: if 0: ¬true then Q;
		apply not_elim[OF 0].

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

end

---
Under Pierce's law, self-refutation principle, consequentia mirabilis and excluded middle coincide.
---
context SelfRefutation begin

	extend PierceLaw begin

		interpret ExcludedMiddle;
			- if PQ: P ⟹ Q, nPQ: ¬P ⟹ Q then Q;
				apply pierce_law[of (¬P)];
				- if QnP: Q ⟹ ¬P then Q;
					apply nPQ;
					apply self_refutation;
					by QnP PQ.
				.
			.

	end

end

context ClaviusLaw begin

	extend PierceLaw begin

		interpret ExcludedMiddle;
			- if PQ: P ⟹ Q, nPQ: ¬P ⟹ Q then Q;
				apply pierce_law[of P];
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
	Under explosiveness, self-refutation implies double-negation introduction.
	---
	extend SelfRefutation begin
		interpret NNotIntro;
			- if P: P then ¬ ¬ P;
				apply self_refutation;
				- if nP: ¬P;
					by not_elim[OF nP P].
				.
			.
	end
	---
	Clavius's law implies Pierce's law, and thus excluded middle.
	---
	extend ClaviusLaw begin

		interpret PierceLaw;
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

	context NotInconsistent begin

		extend ExplosiveNot begin

			interpret SelfRefutation;
				- if PnP: P ⟹ ¬P then ¬P;
					apply not_intro;
					- if P: P then Q;
						apply not_elim[OF PnP[OF P] P].
					.
				.
			interpret NNotIntro.
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

	interpret ExplosiveNot;
		- if nP: ¬P, P: P then Q;
			apply not_imp_sym[OF _ nP];
			by P.
		.

	interpret NNotElim;
		by not_imp_sym[OF imp.refl].

	interpret ContraPos;
		- if imp: P ⟹ Q, nQ: ¬Q then ¬P;
			apply not_imp_sym[OF _ nQ];
			by imp #elim nnot_elim.
		.

	lemma nimp_not_elim1: if nimp: ¬(P ⟹ ¬Q) then P;
		apply nnot_elim;
		apply nimp_not_imp_nnot[OF nimp].

	lemma nimp_not_elim2: if nimp: ¬(P ⟹ ¬Q) then Q;
		apply nnot_elim;
		apply nimp_imp_not[OF nimp].

	lemma nimp_not_elim: if nimp: ¬(P ⟹ ¬Q), PQR: P ⟹ Q ⟹ R then R;
		apply PQR[OF nimp_not_elim1[OF nimp] nimp_not_elim2[OF nimp]].

	lemma nnnot_intro: if not: ¬P then ¬ ¬ ¬P;
		apply not.cmono[OF nnot_elim not].

	extend NotInconsistent begin

		interpret ExplosiveNot.
		---
		Explosivity brings self refutation, which brings consequentia mirabilis, with which explosivity brings excluded middle.
		---
		interpret ClaviusLaw;
			- if imp: ¬P ⟹ P then P;
				apply nnot_elim;
				apply self_refutation;
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
	interpret NotInconsistent.-- This brings the excluded middle
	thm cases.

	interpret InvContraPos;
		- if nPnQ: ¬P ⟹ ¬Q, Q: Q then P;
			apply not_imp_sym[OF nPnQ nnot_intro[OF Q]].
		.

end
