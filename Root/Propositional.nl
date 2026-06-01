---
## Propositional Logics

We fix a class `Prop` in which logical operators are closed.
---
import Magmas.

fix Prop (∧) (∨) (¬) (⟺) false.
import imp: Magma Prop (⟹).
import and: Magma Prop (∧).
import or: Magma Prop (∨).
import not: Unary (¬) Prop Prop.
import iff: Magma Prop (⟺).
assume false_type! false ∈ Prop.

begin

interpret? TypeFree.

note! imp.closed and.closed or.closed not.closed iff.closed.

-- `true` is obtained via `false ⟹ false`.
obtain true where true_intro! true, true_type! true ∈ Prop;
	- for thesis if assm;
		apply assm[of (false ⟹ false)].
	.

interpret iff: Magmas.MetaRelation (⟺).-- Magma notions wrt (⟺)

extend Iff begin

	interpret Prop_iff: Equivalence Prop (⟺);
		-.
		- if xy: x ⟺ y; by iff.sym[OF xy].
		- if xy: x ⟺ y, yz: y ⟺ z; by iff.trans[OF xy yz].
		.

end

extend TypeSafeMinimal begin

	interpret .Iff.

	interpret Prop_and: Prop_iff.CommMonoid (∧) true;
		by and.commute and.left_assoc.

end

theory PierceLaw:
	assume pierce_law: if (P ⟹ Q) ⟹ P, P ∈ Prop, Q ∈ Prop then P.
end

theory Minimal:
	--- Allows elimination rules only derive propositions. ---
	import TypeSafeMinimal.
	assume or_elim: if P ∨ Q, P ⟹ R, Q ⟹ R, R ∈ Prop then R.
	assume ex_elim: if ∃x. P.[x], ∀x. P.[x] ⟹ Q, Q ∈ Prop then Q.
begin

	interpret Prop_or: Symmetric Prop (∨);
		by #elim or_elim.

	interpret Prop_or: Prop_iff.CommMonoMagma (∨);
		-.
		- by iff_intro #elim or_elim.
		- if PQ: P ⟺ Q;
			by iff_intro #elim or_elim #simp PQ.
		.
	note#cong Prop_or.cong.

	interpret Prop_or: Prop_iff.CommSemigroupAbsorb (∨) true;
		by iff_intro #elim or_elim.

	interpret Prop_or: iff.Idempotent Prop (∨);
		by iff_intro #elim or_elim.

	lemma or_imp_iff: if !R ∈ Prop then (P ∨ Q ⟹ R) ⟺ (P ⟹ R) ∧ (Q ⟹ R);
		apply iff_intro;
		- if imp;
			by imp.
		by #elim or_elim.

	lemma imp_or_if: if or: (P ⟹ Q) ∨ (P ⟹ R), !P, !Q ∈ Prop, !R ∈ Prop then Q ∨ R;
		apply or_elim[OF or].

	interpret Prop_and_or: Prop_iff.CommSemiring (∧) (∨);
		-.
		- by and.commute.
		-.
		- by Prop_or.left_mono.
		- by Prop_or.right_mono.
		- if !P ∈ Prop, !Q ∈ Prop, !R ∈ Prop then P ∧ (Q ∨ R) ⟺ P ∧ Q ∨ P ∧ R;
			apply iff_intro;
			simp or_imp_iff imp_and_iff1.
		- by and.left_assoc.
		- by Prop_or.commute.
		- by Prop_or.left_assoc.
		.

	lemma nor_iff: if !P ∈ Prop, !Q ∈ Prop then ¬(P ∨ Q) ⟺ ¬P ∧ ¬Q;
		unfold not_iff_imp_false;
		by or_imp_iff.

	lemma nnot_excluded_middle: if !P ∈ Prop then ¬ ¬(P ∨ ¬P);
		unfold nor_iff;
		by non_contradiction.

	lemma nnot_nor_iff: if !P ∈ Prop, !Q ∈ Prop then ¬ (¬ ¬ P ∨ Q) ⟺ ¬(P ∨ Q);
		unfold nor_iff nnnot_iff.

	lemma nor_nnot_iff: if !P ∈ Prop, !Q ∈ Prop then ¬(P ∨ ¬ ¬ Q) ⟺ ¬(P ∨ Q);
		unfold nor_iff nnnot_iff.

	lemma or_imp_nand: if !P ∈ Prop, !Q ∈ Prop then P ∨ Q ⟹ ¬(¬P ∧ ¬Q);
		by not_intro #elim or_elim.
	---
	## Existence
	---
	lemma ex_imp_all_imp:
		if ex: ∃x. P.[x] ⟹ Q, all: ∀x. P.[x], !Q ∈ Prop then Q;
		apply ex_elim[OF ex];
		- for x if imp: P.[x] ⟹ Q;
			by imp all.
		.
	lemma ex_imp_iff_all#simp
		if ! Q ∈ Prop then ((∃x. P.[x]) ⟹ Q) ⟺ (∀x. P.[x] ⟹ Q);
		apply iff_intro;
		- if imp, Px: P.[x];
			by imp ex_intro1[OF Px].
		- if imp, ex;
			apply ex_elim[OF ex];
			- for x;
				by imp[of x].
			.
		.
	lemma nex_iff_all_not: ¬(∃x. P.[x]) ⟺ (∀x. ¬ P.[x]);
		simp not_iff_imp_false.

	theory ExcludedMiddle:
		assume or_not:
			-- @English excluded middle
			-- @Latin tertium non datur
			if P ∈ Prop then P ∨ ¬P.
	begin

		lemma cases: if PQ: P ⟹ Q, nPQ: ¬P ⟹ Q, P: P ∈ Prop, ! Q ∈ Prop then Q;
			apply or_elim[OF or_not[OF P]];
			- by PQ.
			- by nPQ.
			.

	end

	extend PierceLaw begin
		interpret ExcludedMiddle;
			- for P if ! P ∈ Prop then P ∨ ¬ P;
				apply pierce_law[of _ false];
				- if imp: P ∨ ¬ P ⟹ false;
					apply or_intro2;
					-> if ! P;
						by imp.
					.
				.
			.
	end

end

theory Intuitionistic:
	--- Typed intuitionistic logic allows false imply any *proposition*. ---
	import Minimal.
	assume false_elim: if false, P ∈ Prop then P.
begin

	lemma not_imp_iff_false: if nP: ¬P, !P ∈ Prop then P ⟺ false;
		by iff_intro not_imp_false[OF nP] #elim false_elim.

	lemma false_imp_iff#simp if ! P ∈ Prop then (false ⟹ P) ⟺ true;
		by iff_true #elim false_elim.

	interpret Prop_and: Prop_iff.CommMonoidAbsorb (∧) false true;
		by iff_intro #elim false_elim.

	interpret Prop_or: Prop_iff.CommMonoidAbsorb (∨) true false;
		by iff_intro #elim or_elim false_elim.

	note#simp Prop_and.left_absorb Prop_and.right_absorb
		Prop_or.left_neutral Prop_or.right_neutral.

	lemma not_elim: if nP: ¬P, P: P, ! Q ∈ Prop then Q;
		apply false_elim;
		by not_imp_false[OF nP P].

end

theory Classical:
	import Minimal.
	assume nnot_imp:
		-- @English double negation elimination
		if ¬ ¬ P, P ∈ Prop then P.
begin

	lemma nnot_iff#simp if ! P ∈ Prop then ¬ ¬ P ⟺ P;
		by iff_intro nnot_intro #elim nnot_imp.

	lemma or_iff_nand: if ! P ∈ Prop, ! Q ∈ Prop then P ∨ Q ⟺ ¬ (¬P ∧ ¬Q);
		fold nor_iff.

	lemma contradiction:
		-- @Latin reductio ad absurdum
		(¬P ⟹ false) ⟹ P ∈ Prop ⟹ P;
		fold not_iff_imp_false;
		by #elim nnot_imp.

	interpret Intuitionistic;
		- if 0: false, ! P ∈ Prop;
			apply contradiction;
			by 0.
		.
	interpret PierceLaw;
		- if PQP: (P ⟹ Q) ⟹ P, ! P ∈ Prop, ! Q ∈ Prop then P;
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

context Intuitionistic begin

	extend ExcludedMiddle begin
		interpret Classical;
			- if nnP: ¬ ¬ P, ! P ∈ Prop then P;
				apply cases[of P];
				- if nP: ¬P;
					apply not_elim[OF nnP nP].
				.
			.
	end

end
