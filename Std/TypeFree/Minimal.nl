---
# Type-Free Minimal Logic
---
import TypeSafeMinimal.
assume or_elim: if P ∨ Q, P ⟹ R, Q ⟹ R then R.
assume ex_elim: if ∃x. P.[x], ∀x. P.[x] ⟹ Q then Q.

begin

---
## Disjunction
---

lemma or_iff: P ∨ Q ⟺ (∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R);
	apply iff_intro[OF or_elim or_intro].

interpret or: MetaSymmetric (∨);
	by #elim or_elim.

---
Algebraic properties of `(∨)`, with respect to `(⟺)`.
Minimal logic does not allow `false` to be neutral of or: `false ∨ P ⟺ P`,
because the `false` case does not derive `P`.
---
interpret or: iff.MetaCompatible (∨);
	- if PQ: P ⟺ Q, RS: R ⟺ S then P ∨ R ⟺ Q ∨ S;
		by iff_intro #elim or_elim #simp PQ RS.
	.
note#cong or.cong.

interpret or: iff.MetaCommSemigroupAbsorb (∨) true;
	by iff_intro #elim or_elim #simp or_iff_true1 or_iff_true2.

interpret or: iff.MetaIdempotent (∨);
	- show: P ∨ P ⟺ P;
		by iff_intro #elim or_elim.
	.

note#simp or.idem.

lemma or_imp_iff: (P ∨ Q ⟹ R) ⟺ (P ⟹ R) ∧ (Q ⟹ R);
	apply iff_intro;
	- if imp;
		by imp.
	by #elim or_elim.

lemma imp_or_if: if or: (P ⟹ Q) ∨ (P ⟹ R), !P then Q ∨ R;
	by or[unfold imp_imp_iff].

lemma and_or_distrib: P ∧ (Q ∨ R) ⟺ P ∧ Q ∨ P ∧ R;
	apply iff_intro;
	simp or_imp_iff.

lemma or_and_distrib: (P ∨ Q) ∧ R ⟺ P ∧ R ∨ Q ∧ R;
	unfold and.commute;
	unfold and_or_distrib.

lemma nor_iff: ¬ (P ∨ Q) ⟺ ¬P ∧ ¬Q;
	unfold not_iff_imp_false;
	by or_imp_iff.

lemma nnot_or_not: ¬ ¬ (P ∨ ¬P);
	unfold nor_iff;
	by non_contradiction.

lemma nnot_nor_iff: ¬ (¬ ¬ P ∨ Q) ⟺ ¬ (P ∨ Q);
	unfold nor_iff nnnot_iff.

lemma nor_nnot_iff: ¬ (P ∨ ¬ ¬ Q) ⟺ ¬ (P ∨ Q);
	unfold nor_iff nnnot_iff.

lemma or_imp_nand: P ∨ Q ⟹ ¬ (¬P ∧ ¬Q);
	by not_intro #elim or_elim.

---
## Existence
---

lemma ex_imp_iff_all#simp#rule ((∃x. P.[x]) ⟹ Q) ⟺ (∀x. P.[x] ⟹ Q);
	apply iff_intro;
	- if imp: (∃x. P.[x]) ⟹ Q, Px: P.[x];
		by imp ex_intro1[OF Px].
	- if imp: ∀x. P.[x] ⟹ Q;
		by #elim imp ex_elim.
	.

lemma ex_iff: (∃x. P.[x]) ⟺ (∀Q. (∀x. P.[x] ⟹ Q) ⟹ Q);
	apply iff_intro;
	- apply ex_elim>0.
	- apply ex_intro>0.
	.

lemma ex_cong#cong#rule_cong if eq: ∀x. P.[x] ⟺ P'.[x] then (∃x. P.[x]) ⟺ (∃x. P'.[x]);
	unfold ex_iff eq.

lemma ex_indep#simp (∃x. P) ⟺ P;
	by iff_intro ex_intro1 #elim ex_elim.

lemma ex_and1#rule (∃x. P.[x]) ∧ Q ⟺ (∃x. P.[x] ∧ Q);
	simp iff_iff_and imp_and_distrib;
	- for x;
		by ex_intro1[of x].
	.

lemma ex_and2#rule P ∧ (∃x. Q.[x]) ⟺ (∃x. P ∧ Q.[x]);
	simp iff_iff_and imp_and_distrib;
	- for x;
		by ex_intro1[of x].
	.

lemma ex_or_distrib: (∃x. P.[x] ∨ Q.[x]) ⟺ (∃x. P.[x]) ∨ (∃x. Q.[x]);
	simp iff_iff_and or_imp_iff all_and_distrib[dual];
	- for x;
		by ex_intro1[of x].
	.

lemma nex_iff_all_not: ¬ (∃x. P.[x]) ⟺ (∀x. ¬ P.[x]);
	simp not_iff_imp_false.

---
## Theories
---
extend MetaRelation begin

	extend ExRel begin
		lemma ex_elim: if ex: ∃x ⊏ a. P.[x], imp: ∀x. x ⊏ a ⟹ P.[x] ⟹ Q then Q;
			apply ex[unfold ex_iff, THEN ex_elim];
			- for x;
				by imp[of x].
			.
		lemma ex_cong_strong:
			if a: ∀x. x ⊏ a ⟺ x ⊏ a', P: ∀x. x ⊏ a' ⟹ (P.[x] ⟺ P'.[x])
			then (∃x ⊏ a. P.[x]) ⟺ (∃x ⊏ a'. P'.[x]);
			unfold+ ex_iff; unfold a; unfold P.

		lemma ex_cong_weak:
			if P: ∀x. x ⊏ a ⟹ (P.[x] ⟺ P'.[x]) then (∃x ⊏ a. P.[x]) ⟺ (∃x ⊏ a. P'.[x]);
			unfold+ ex_iff P.

		lemma ex_imp_iff: ((∃x ⊏ a. P.[x]) ⟹ Q) ⟺ (∀x. x ⊏ a ⟹ P.[x] ⟹ Q);
			apply iff_intro;
			- if imp, x: x ⊏ a, Px: P.[x];
				apply imp ex_intro1[OF x Px].
			- if all, ex;
				apply ex_elim[OF ex];
				- for x if x, Px;
					apply all[OF x Px].
				.
			.
		lemma ex_or_distrib: (∃x ⊏ a. P.[x] ∨ Q.[x]) ⟺ (∃x ⊏ a. P.[x]) ∨ (∃x ⊏ a. Q.[x]);
			simp ex_iff and_or_distrib .ex_or_distrib.

		lemma ex_iff_all: (∃x ⊏ a. P.[x]) ⟺ (∀Q. (∀x. x ⊏ a ⟹ P.[x] ⟹ Q) ⟹ Q);
			unfold ex_iff Minimal.ex_iff.

	end

	extend AllRel begin -- TODO: automate?
		extend ExRel begin
			lemma ex_imp_iff_all: ((∃x ⊏ a. P.[x]) ⟹ Q) ⟺ (∀x ⊏ a. P.[x] ⟹ Q);
				simp ex_iff all_iff ex_imp_iff.
			lemma nex_iff_all_not: ¬ (∃x ⊏ a. P.[x]) ⟺ (∀x ⊏ a. ¬ P.[x]);
				unfold ex_iff all_iff .nex_iff_all_not nand_iff_imp_not.
		end
	end
end

extend Membership begin
	interpret in: Minimal.MetaRelation (∈).
	interpret in: in.AllRel (∀∈).
	interpret in: in.ExRel (∃∈).

	note#rule in.all_iff.
	note#rule in.ex_imp_iff.
	note#simp in.ex_imp_iff_all.
	note#elim in.ex_elim.

end

theory ExcludedMiddle :=
	assume or_not:
		-- @English excluded middle
		-- @Latin tertium non datur
		P ∨ ¬P.
begin -- This is incomparable with Explosion, but their combination leads to classical logic.

	interpret NotCases;
		- if PQ: P ⟹ Q, nPQ: ¬P ⟹ Q then Q;
			apply or_elim[OF or_not[of P]];
			- by PQ.
			- by nPQ.
			.
		.

end

extend NotCases begin
	interpret ExcludedMiddle;
		- show: P ∨ ¬P;
			apply cases[of P].
		.
end


-- Pierce Law implies Excluded Middle.
extend PierceLaw begin
	interpret ExcludedMiddle;
		- for P then P ∨ ¬ P;
			apply pierce_law[of _ false];
			- if imp: P ∨ ¬ P ⟹ false;
				apply or_intro2;
				-> if ! P;
					by imp.
				.
			.
		.
end

theory Explosion :=
	assume false_elim: if false then P.
begin
	interpret False;
		retain false;
			by false_elim.
		.

	lemma not_elim: if nP: ¬P, P: P then Q;
		use not_imp_false[OF nP P].

	lemma not_imp_iff_false: if nP: ¬P then P ⟺ false;
		by iff_intro not_imp_false[OF nP].

	lemma false_imp_iff#simp (false ⟹ P) ⟺ true;
		by iff_true.

	interpret and: iff.MetaCommAbsorb (∧) false;
		by iff_intro.

	note#simp and.left_absorb and.right_absorb.

	interpret or: iff.MetaCommNeutral (∨) false;
		by iff_intro or_intro #elim or_elim false_elim.

	note#simp or.left_neutral or.right_neutral.

	extend ExcludedMiddle begin
		interpret DoubleNegation;
			- if nnP: ¬ ¬ P then P;
				apply cases[of P];
				- if nP: ¬P;
					by not_elim[OF nnP nP].
				.
			.
	end

end

extend DoubleNegation begin

	lemma nnot_iff#simp ¬ ¬ P ⟺ P;
		apply iff_intro[OF nnot_imp nnot_intro].

	lemma contradiction:
		-- @Latin reductio ad absurdum
		if assm: ¬P ⟹ false then P;
		apply nnot_imp;
		apply not_intro;
		by assm.

	lemma or_iff_nand: P ∨ Q ⟺ ¬ (¬P ∧ ¬Q);
		fold nor_iff.

	interpret Explosion;
		- if 0: false then P;
			apply contradiction;
			by 0.
		.

	interpret PierceLaw;
		- if PQP: (P ⟹ Q) ⟹ P then P;
			apply nnot_imp;
			-> if nP: ¬P then false;
				apply not_imp_false[OF nP];
				apply PQP;
				- if P: P then Q;
					by not_elim[OF nP P].
				.
			.
		.

end
