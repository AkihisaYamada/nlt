---
# Logic on Binary Abbreviation
---
import Eq.
import Pair.
assume abbrev2: if ∀f. (∀x y. f x y = F.[(x,y)]) ⟹ P then P.

begin

--- This allows unary and multi-ary abbreviation. ---
interpret UnaryAbbreviation;
	- for F P if assm;
		note(cong) eq.cong_meta[of F].
		apply abbrev2[of (p. F.[snd p])];
		- for f if f;
			by assm[of (f fst)] #unfold f snd.
		.
	.
lemma abbrev3: if assm: ∀f. (∀x y z. f x y z = F.[(x,y,z)]) ⟹ P then P;
	note(cong) eq.cong_meta[of F].
	apply abbrev2[of (t. F.[(fst (fst t), snd (fst t), snd t)])];
	- for f2 if f2;
		apply abbrev2[of (p. f2 p)];
		- for f3 if f3;
			by assm[of f3] #unfold f3 f2 fst snd.
		.
	.
--- One can obtain type-free binary logical operators by abbreviation. ---
interpret Iff;
	obtain (⟺) where
		iff_intro: (P ⟹ Q) ⟹ (Q ⟹ P) ⟹ (P ⟺ Q),
		iff_elim1: (P ⟺ Q) ⟹ P ⟹ Q,
		iff_elim2: (P ⟺ Q) ⟹ Q ⟹ P;
		- for thesis if assm;
			apply abbrev2[of (p. ∀R. ((fst p ⟹ snd p) ⟹ (snd p ⟹ fst p) ⟹ R) ⟹ R)];
			- for f if f;
				apply assm[of f];
				- for P Q if PQ, QP;
					unfold f;
					- for R if body;
						apply body[unfolded fst snd];
						-; by PQ.
						-; by QP.
						.
					.
				- for P Q if fPQ, P;
					apply fPQ[unfolded f];
					unfold fst snd;
					- if PQ, QP;
						by PQ[OF P].
					.
				- for P Q if fPQ, Q;
					apply fPQ[unfolded f];
					unfold fst snd;
					- if PQ, QP;
						by QP[OF Q].
					.
				.
			.
		.
	.

interpret Intuitionistic;
	obtain true where true_intro: true;
		- for thesis if assm;
			apply assm[of (∀P. P ⟹ P)].
		.
	obtain false where false_elim: false ⟹ ∀P. P;
		- for thesis if assm;
			apply assm[of (∀P. P)].
		.
	obtain (∧) where
		and_intro: P ⟹ Q ⟹ P ∧ Q,
		and_elim1: P ∧ Q ⟹ P,
		and_elim2: P ∧ Q ⟹ Q;
		- for thesis if assm;
			apply abbrev2[of (p. ∀R. (fst p ⟹ snd p ⟹ R) ⟹ R)];
			- for f if f;
				apply assm[of f, unfolded f fst snd].
			.
		.
	obtain (∨) where
		or_intro1: ∀P Q. P ⟹ P ∨ Q,
		or_intro2: ∀P Q. Q ⟹ P ∨ Q,
		or_elim: P ∨ Q ⟹ ∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R;
		- for thesis if assm;
			apply abbrev2[of (p. ∀R. (fst p ⟹ R) ⟹ (snd p ⟹ R) ⟹ R)];
			- for f if f;
				apply assm[of f, unfolded f fst snd];
				-; by #unfold imp_imp_iff.
				-; by #unfold imp_imp_iff.
				- for P Q; apply imp.refl=.
				.
			.
		.
	obtain (¬) where
		not_intro: (P ⟹ false) ⟹ ¬P,
		not_imp_false: ¬P ⟹ P ⟹ false;
		- for thesis if assm;
			apply abbrev[of (P. P ⟹ false)];
			- for f if f;
				apply assm[of f, unfolded f].
			.
		.
	.
theory Membership:
	import Membership.
begin
	obtain (⊆) where subseteq_iff: X ⊆ Y ⟺ (∀x ∈ X. x ∈ Y);
		- for thesis if assm;
			apply abbrev2[of (p. ∀x ∈ fst p. x ∈ snd p)];
			- for f if f;
				by assm[of f] #unfold f fst snd.
			.
		.
	obtain (∉) where notin_iff: x ∉ X ⟺ ¬ x ∈ X;
		- for thesis if assm;
			apply abbrev2[of (p. ¬ fst p ∈ snd p)];
			- for f if f;
				apply assm[of f];
				by iff_intro #unfold f fst snd.
			.
		.
end

interpret Const;
	obtain const where const_eq: const x y = x;
		- for thesis if elim;
			apply abbrev2[of (p. fst p)];
			- for f if f;
				by elim[of f] #unfold f fst.
			.
		.
	.
lemma curry: for f, ∃f'. ∀x y. f' x y = f (x,y);
	apply abbrev2[of (p. f p)];
	- for f' if f';
		by ex_intro1[of f'] #unfold f' fst snd.
	.
obtain inverts where
	inverts_intro: (∀x. f (g x) = x) ⟹ inverts f g,
	inverts_elim1: inverts f g ⟹ ∀x. f (g x) = x;
	- for thesis if assm;
		apply abbrev2[of (p. ∀x. fst p (snd p x) = x)];
		- for inverts if inverts;
			apply assm[of inverts, unfolded inverts fst snd].
		.
	.
obtain rev_app where rev_app: rev_app x f = f x;
	- for thesis if assm;
		apply abbrev2[of (p. snd p (fst p))];
		- for f if f;
			by assm[of f] #unfold f fst snd.
		.
	.

obtain (≠) where neq_iff: x ≠ y ⟺ ¬ x = y;
	- for thesis if assm;
		apply abbrev2[of (p. ¬ fst p = snd p)];
		- for f if f;
			by assm[of f] #unfold f fst snd.
		.
	.

obtain sup_pred where sup_pred_iff: sup_pred P Q x ⟺ P x ∨ Q x;
	- for thesis if assm;
		apply abbrev3[of (t. fst t (snd (snd t)) ∨ fst (snd t) (snd (snd t)))];
		- for f if f;
			by assm[of f] #unfold f fst snd.
		.
	.
obtain inf_pred where inf_pred_iff: inf_pred P Q x ⟺ P x ∧ Q x;
	- for thesis if assm;
		apply abbrev3[of (t. fst t (snd (snd t)) ∧ fst (snd t) (snd (snd t)))];
		- for f if f;
			by assm[of f] #unfold f fst snd.
		.
	.

theory Collect:
	import Collect.
begin
	interpret Membership.
	obtain Empty where Empty_def: Empty = {x. false};
		- for thesis if assm;
			apply assm[OF eq.refl].
		.
	lemma not_in_Empty: ¬ x ∈ Empty;
		by not_false #unfold Empty_def in_COLLECT_iff const_eq.

	obtain Singleton where Singleton_def: Singleton x = {y. x = y};
		- for thesis if assm;
			apply abbrev[of (x. {y. x = y})];
			- for f if f;
				by assm[of f] #unfold f.
			.
		.
	lemma in_Singleton_iff: x ∈ Singleton y ⟺ x = y;
		unfold Singleton_def in_COLLECT_iff;
		apply iff.eq.commute.

	obtain UNIV where UNIV_def: UNIV = {x. true};
		- for thesis if assm;
			apply assm[OF eq.refl].
		.
	lemma in_UNIV! x ∈ UNIV;
		unfold UNIV_def in_COLLECT_iff const_eq.

	obtain (⋃) where bigcup_def: ⋃XX = {x. ∃X ∈ XX. x ∈ X};
		- for thesis if assm;
			apply abbrev[of (XX. {x. ∃X ∈ XX. x ∈ X})];
			- for f if f;
				by assm[of f] #unfold f.
			.
		.
	lemma in_bigcup_iff: x ∈ ⋃XX ⟺ (∃X ∈ XX. x ∈ X);
		unfold bigcup_def in_COLLECT_iff.
	obtain (⋂) where bigcap_def: ⋂XX = {x. ∀X ∈ XX. x ∈ X};
		- for thesis if assm;
			apply abbrev[of (XX. {x. ∀X ∈ XX. x ∈ X})];
			- for f if f;
				by assm[of f] #unfold f.
			.
		.
	lemma in_bigcap_iff: x ∈ ⋂XX ⟺ (∀X ∈ XX. x ∈ X);
		by #unfold bigcap_def in_COLLECT_iff.

end


theory Class:
	import Collect.
	assume COLLECT_ext: (∀x. P.[x] ⟺ Q.[x]) ⟹ {x. P.[x]} = {x. Q.[x]}.
begin

	lemma COLLECT_eq_iff: {x. P.[x]} = {x. Q.[x]} ⟺ (∀x. P.[x] ⟺ Q.[x]);
		apply iff_intro;
		- if eq;
			unfold eq.
		apply COLLECT_ext=.

	obtain (∪) where cup_def: X ∪ Y = {x. x ∈ X ∨ x ∈ Y};
		- for thesis if assm;
			apply abbrev2[of (p. {x. x ∈ fst p ∨ x ∈ snd p})];
			- for f if f;
				by assm[of f] #unfold f fst snd.
			.
		.
	lemma in_cup_iff: x ∈ X ∪ Y ⟺ x ∈ X ∨ x ∈ Y;
		unfold cup_def in_COLLECT_iff.

	set set_comprehension COLLECT Empty Singleton (∪).

	obtain (∩) where cap_def: X ∩ Y = {x. x ∈ X ∧ x ∈ Y};
		- for thesis if assm;
			apply abbrev2[of (p. {x. x ∈ fst p ∧ x ∈ snd p})];
			- for f if f;
				by assm[of f] #unfold f fst snd.
			.
		.

end

	obtain DECIDED where DECIDED_def: DECIDED = {x. x ∨ ¬x};
		- for thesis if assm;
			apply assm[OF eq.refl].

	lemma in_DECIDED_iff: P ∈ DECIDED ⟺ P ∨ ¬P;
		unfold DECIDED_def in_COLLECT_iff.

	namespace DECIDED begin

		interpret Propositional (∈) DECIDED;
		- for x y if x: x ∈ DECIDED, y: y ∈ DECIDED then (x ⟹ y) ∈ DECIDED;
			unfold in_DECIDED_iff;
			apply or_elim[OF y[unfolded in_DECIDED_iff]];
			-; by or_intro1.
			- if ny: ¬y;
				apply or_elim[OF x[unfolded in_DECIDED_iff]];
				- if !x;
					apply+ or_intro2 not_intro;
					by not_imp_false[OF ny].
				- if nx: ¬x;
					apply or_intro1[OF not_elim[OF nx]].
				.
			.
		.

		interpret Classical;
			note! not_intro and_intro or_intro iff_intro.
			note #elim: and_elim or_elim iff_elim false_elim.

		- false ∈ DECIDED;
			by not_false #unfold in_DECIDED_iff.
		- for x, x ∈ DECIDED ⟹ (¬ x) ∈ DECIDED;
			by nnot_intro #unfold in_DECIDED_iff.
			show and_type: for x y, x ∈ DECIDED ⟹ y ∈ DECIDED ⟹ (x ∧ y) ∈ DECIDED;
				unfold+ in_DECIDED_iff;
				if x: x ∨ ¬x, y: y ∨ ¬y;
					apply or_elim[OF x];
					if !x;
						apply or_elim[OF y];
						- by or_intro1 and_intro.
						by or_intro2 nand_intro2.
					by or_intro2 nand_intro1.
				.
		- for x y, x ∈ DECIDED ⟹ y ∈ DECIDED ⟹ (x ∨ y) ∈ DECIDED;
			unfold+ in_DECIDED_iff;
			- if x: x ∨ ¬x, y: y ∨ ¬y;
				apply or_elim[OF x];
				-; by or_intro1.
				- if ! ¬x;
					apply or_elim[OF y];
					- if ! y;
						apply or_intro1;
						by or_intro2.
					- if ! ¬y;
						apply or_intro2;
						unfold nor_iff;
						by and_intro.
					.
				.
			.
		- for x y, x ∈ DECIDED ⟹ y ∈ DECIDED ⟹ (x ⟺ y) ∈ DECIDED;
			unfold iff_def;
			by and_type imp_type.
		- for P if P0: P ⟹ false, _ then ¬ P;
			by P0.
		- for P, ¬ P ⟹ P ⟹ P ∈ DECIDED ⟹ false;
			by #elim not_imp_false.
		retain true := true;
			by or_intro #unfold in_DECIDED_iff.
		-  for P, P ∈ DECIDED ⟹ P ∨ ¬ P;
			unfold in_DECIDED_iff.
		.

	end

	thm DECIDED.pierce_law.

	lemma nnot_DECIDED: ¬ ¬ x ∈ DECIDED;
		unfold in_DECIDED_iff;
		by nnot_excluded_middle.


end

theory weakCollect:
begin
	interpret Collect;
		obtain COLLECT_in_pair where
			COLLECT_in_pair: snd COLLECT_in_pair x (fst COLLECT_in_pair P) ⟺ P x;
			- for thesis if assm;
				apply assm[of (id,rev_app)];
				by #unfold fst snd rev_app.
			.
		obtain COLLECT where COLLECT_def: COLLECT = fst COLLECT_in_pair;
			- for thesis if assm;
				apply assm[OF eq.refl].
			.
		obtain (∈) where in_def: (∈) = snd COLLECT_in_pair;
			- for thesis if assm;
				apply assm[OF eq.refl].
			.
		by #unfold Collect_def in_def Collect_in_pair.
end


---
Having operator `THE` yields `If`.
---
theory The:
	import The.
begin
	interpret If;
		obtain If where
			If_then: P ⟹ If P x y = x,
			If_else: (P ⟹ x = y) ⟹ If P x y = y;
			- for thesis if assm;
				apply abbrev3[of (t. THE z. fst t ∧ z = fst (snd t) ∨ (fst t ⟹ fst (snd t) = snd (snd t)) ∧ z = snd (snd t))];
				- for If if If;
					apply assm[of If, unfolded If];
					- for P x y if P: P;
						apply THE_eq_intro;
						-; unfold fst snd;
							apply ex1_intro1[of x];
							-;
								by or_intro1 P.
							- for z if or;
								apply or_elim[OF or];
								-; .
								-; unfold and_imp_iff_imp_imp imp_imp_iff[OF P];
									- if xy, zy;
										unfold xy zy.
									.
								.
							.
						-; unfold fst snd;
							by or_intro1 P.
						.
					- for P x y if nP: P ⟹ x = y;
						apply THE_eq_intro;
						-; unfold fst snd;
							apply ex1_intro1[of y];
							-; unfold imp_and_iff1[OF nP] or_iff_true2.
							- for z if or;
								apply or_elim[OF or];
								unfold and_imp_iff_imp_imp;
								- if P: P, zx: z = x then z = y;
									unfold nP[OF P] zx.
								.
							.
						-; unfold fst snd;
							by or_intro2 nP.
						.
					.
				.
			.
		.
end

end
