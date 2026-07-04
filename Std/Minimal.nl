---
# Type-Free Minimal Logic
---
fix false (∧) (∨) (¬) (⟺) (∃).
import And.
import Not.
import Iff.
assume or_intro1: for P Q if P then P ∨ Q.
assume or_intro2: for P Q if Q then P ∨ Q.
assume or_elim: if P ∨ Q, P ⟹ R, Q ⟹ R then R.
assume ex_intro1: for x if P.[x] then ∃x. P.[x].
assume ex_elim: if ∃x. P.[x], ∀x. P.[x] ⟹ Q then Q.

begin

interpret TypeSafeMinimal.
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
			apply ex[unfold ex_def, THEN ex_elim];
			- for x;
				by imp[of x].
			.
		lemma ex_cong_strong:
			if a: ∀x. x ⊏ a ⟺ x ⊏ a', P: ∀x. x ⊏ a' ⟹ (P.[x] ⟺ P'.[x])
			then (∃x ⊏ a. P.[x]) ⟺ (∃x ⊏ a'. P'.[x]);
			unfold+ ex_def; unfold a; unfold P.
		lemma ex_cong_weak:
			if P: ∀x. x ⊏ a ⟹ (P.[x] ⟺ P'.[x]) then (∃x ⊏ a. P.[x]) ⟺ (∃x ⊏ a. P'.[x]);
			unfold+ ex_def P.
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
			simp ex_def and_or_distrib .ex_or_distrib.
		lemma ex_iff: (∃x ⊏ a. P.[x]) ⟺ (∀Q. (∀x. x ⊏ a ⟹ P.[x] ⟹ Q) ⟹ Q);
			unfold ex_def ex_iff.

	end

	extend AllRel begin -- TODO: automate?
		extend ExRel begin
			lemma ex_imp_iff_all: ((∃x ⊏ a. P.[x]) ⟹ Q) ⟺ (∀x ⊏ a. P.[x] ⟹ Q);
				simp ex_def all_iff ex_imp_iff.
			lemma nex_iff_all_not: ¬ (∃x ⊏ a. P.[x]) ⟺ (∀x ⊏ a. ¬ P.[x]);
				unfold ex_def all_iff .nex_iff_all_not nand_iff_imp_not.
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

	lemma cases: if PQ: P ⟹ Q, nPQ: ¬P ⟹ Q then Q;
		apply or_elim[OF or_not[of P]];
		- by PQ.
		- by nPQ.
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
