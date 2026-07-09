
---
## Negation

We consider negation as primitive, rather than as a derived notion of `false`.
This view allows to declare explosive `false` without exploding every contradiction `P ∧ ¬P`.
The following is a very mild assumption on negation, but retains many important theorems of
minimal logic.
---
fix (¬).
assume imp_not_sym: if P ⟹ ¬Q then Q ⟹ ¬P.

begin

lemma not_intro_connect: if P: P, QnP: Q ⟹ ¬P then ¬Q;
	apply imp_not_sym[OF QnP P].

theorem nnot_intro:-- @English Double Negation Introduction
	if P: P then ¬ ¬ P;
	apply not_intro_connect[OF P].

lemma imp_imp_not_imp_not: if PQ: P ⟹ Q then ¬Q ⟹ ¬P;
	- if nQ;
		apply not_intro_connect[OF nQ];
		by nnot_intro PQ.
	.
lemma not_imp_imp_not: if nP: ¬P, QP: Q ⟹ P then ¬Q;
	by imp_imp_not_imp_not[OF QP nP].

lemma not_imp_nimp: if P: P, nQ: ¬Q then ¬(P ⟹ Q);
	apply not_intro_connect[OF nQ];
	- if PQ: P ⟹ Q then ¬ ¬ Q;
		by nnot_intro PQ P.
	.

lemma self_refutation: if 1: P ⟹ ¬P then ¬P;
	apply not_intro_connect[OF 1];
	by not_imp_nimp nnot_intro.

lemma nnot_imp_imp: if imp: ¬ ¬ P ⟹ Q then P ⟹ Q;
	by imp nnot_intro.

lemma not_intro:-- @English Explosive Negation Introduction
	if expl: P ⟹ ∀Q. Q then ¬P;
	apply not_intro_connect[of (∀R. R ⟹ R)];
	- if P: P;
		apply expl[OF P].
	.

theorem not_inconsistent: ¬(∀Q. Q);
	by not_intro.

theorem nnnot_imp_not:
	-- @English Triple Negation Elimination
	if nnnP: ¬ ¬ ¬ P then ¬P;
	apply not_intro_connect[OF nnnP];
	by nnot_intro.

lemma nnimp_imp_nnot: if nnPQ: ¬ ¬ (P ⟹ Q), P: P then ¬ ¬ Q;
	apply not_intro_connect[OF nnPQ];
	- if nQ: ¬Q then ¬ ¬ ¬ (P ⟹ Q);
		apply nnot_intro;
		apply not_imp_nimp[OF P nQ].
	.


theory MetaIrreflexive (⊏) :=
	assume irrefl: ¬ x ⊏ x.
end

theory MetaAsymmetric (⊏) :=
	assume asym: x ⊏ y ⟹ ¬ y ⊏ x.
end
---
Note that antisymmetry is not yet definable, because it requires equality.
---

theory MetaOrder :=
	import MetaIrreflexive.
	import MetaTransitive.
begin
	interpret MetaAsymmetric;
		- for x y if xy: x ⊏ y then ¬ y ⊏ x;
			apply not_intro_connect[of (¬ x ⊏ x)];
			- by irrefl.
			- if yx: y ⊏ x then ¬ ¬ x ⊏ x;
				apply nnot_intro;
				by trans[OF xy yx].
			.
		.
end

---
Intuitionistic logic makes false explosive; in the false-free formulation, admits
negation elimination `¬P ⟹ P ⟹ Q`. This corresponds to Nelson's system N3.
---
theory ExplosiveNot :=
	assume not_elim: if ¬P, P then Q.
end

---
The explosive negation is so strong that having any `P` and `¬P` collapses the
entire theory. One can consider the following weaker form.
---
theory ImplosiveNot :=
	assume nnot_not_imp: if ¬ ¬ P, ¬P then P.
end


theory MinimalNot :=
	assume not_elim_not: if ¬P, P then ¬Q.
begin

end

context ExplosiveNot begin

	interpret ImplosiveNot;
		- if nnP: ¬ ¬ P, nP: ¬P then P;
			apply not_elim[OF nnP nP].
		.

end

---
A stronger and popular assumption is double-negation elimination (DNE) `¬ ¬ P ⟹ P`.
While DNE collapses traditional minimal logic to classical logic, the false-free formulation
avoids this collapse (Nelson's system N4).
---
theory InvolutiveNot := -- @aka Strong Negation
	assume nnot_imp:
		-- @English Double Negation Elimination
		if ¬ ¬ P then P.
begin

	interpret ImplosiveNot;
		by #elim nnot_imp.

	lemma not_imp_not_imp: if nPQ: ¬P ⟹ Q, nQ: ¬Q then P;
		apply nnot_imp;
		apply not_intro_connect[OF nQ];
		- if nP: ¬P then ¬ ¬ Q;
			apply nnot_intro[OF nPQ[OF nP]].
		.

end

theory ClaviusLaw :=
	assume not_imp_imp:
		-- @English Clavius's Law
		-- @Latin Consequentia Mirabilis
		if ¬P ⟹ P then P.
end

context ImplosiveNot begin
	extend ClaviusLaw begin
		interpret InvolutiveNot;
			- if nnP: ¬ ¬ P then P;
				apply not_imp_imp;
				- if nP: ¬P;
					apply nnot_not_imp[OF nnP nP].
				.
			.
	end
end

theory NotCases :=-- Equivalent to Excluded Middle
	assume cases: if P ⟹ Q, ¬P ⟹ Q then Q.
begin

	interpret ClaviusLaw;
		- if nPP: ¬P ⟹ P then P;
			by cases[OF _ nPP].
		.

end
