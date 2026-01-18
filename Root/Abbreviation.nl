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
			by assm[of (f fst)] #unfold f.
		.
	.
lemma abbrev3: if assm: ∀f. (∀x y z. f x y z = F.[(x,y,z)]) ⟹ P then P;
	note(cong) eq.cong_meta[of F].
	apply abbrev2[of (t. F.[(fst (fst t), snd (fst t), snd t)])];
	- for f2 if f2;
		apply abbrev2[of (p. f2 p)];
		- for f3 if f3;
			by assm[of f3] #unfold f3 f2.
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
interpret Const;
	obtain const where const_eq: const x y = x;
		- for thesis if elim;
			apply abbrev2[of (p. fst p)];
			- for f if f;
				by elim[of f] #unfold f.
			.
		.
	.
lemma curry: for f, ∃f'. ∀x y. f' x y = f (x,y);
	apply abbrev2[of (p. f p)];
	- for f' if f';
		by ex_intro1[of f'] #unfold f'.
	.
obtain inverts where
	inverts_intro: (∀x. f (g x) = x) ⟹ inverts f g,
	inverts_elim1: inverts f g ⟹ ∀x. f (g x) = x;
	- for thesis if assm;
		apply abbrev2[of (p. ∀x. fst p (snd p x) = x)];
		- for f if f;
			by assm[of f] #unfold f.
		.
	.
obtain rev_app where rev_app: rev_app x f = f x;
	- for thesis if assm;
		apply abbrev2[of (p. snd p (fst p))];
		- for f if f;
			by assm[of f] #unfold f.
		.
	.

obtain (≠) where neq_iff: x ≠ y ⟺ ¬ x = y;
	- for thesis if assm;
		apply abbrev2[of (p. ¬ fst p = snd p)];
		- for f if f;
			by assm[of f] #unfold f.
		.
	.

obtain sup_pred where sup_pred_iff: sup_pred P Q x ⟺ P x ∨ Q x;
	- for thesis if assm;
		apply abbrev3[of (t. fst t (snd (snd t)) ∨ fst (snd t) (snd (snd t)))];
		- for f if f;
			by assm[of f] #unfold f.
		.
	.
obtain inf_pred where inf_pred_iff: inf_pred P Q x ⟺ P x ∧ Q x;
	- for thesis if assm;
		apply abbrev3[of (t. fst t (snd (snd t)) ∧ fst (snd t) (snd (snd t)))];
		- for f if f;
			by assm[of f] #unfold f.
		.
	.

theory Membership:
	import ..Membership.
begin
	interpret Membership;
goals.

	obtain (⊆) where subseteq_iff: X ⊆ Y ⟺ (∀x ∈ X. x ∈ Y);
		- for thesis if assm;
			apply abbrev2[of (p. ∀x ∈ fst p. x ∈ snd p)];
			- for f if f;
				by assm[of f] #unfold f.
			.
		.
	obtain (∉) where notin_iff: x ∉ X ⟺ ¬ x ∈ X;
		- for thesis if assm;
			apply abbrev2[of (p. ¬ fst p ∈ snd p)];
			- for f if f;
				apply assm[of f];
				by iff_intro #unfold f.
			.
		.
end

theory Collect:
	import Membership.
	import Collect.
begin
	set compr {} := Empty.
	obtain Empty where Empty_def: {} = {x. false};
		- for thesis if assm;
			apply assm[OF eq.refl].
		.
	lemma not_in_Empty: ¬ x ∈ {};
		by #unfold Empty_def in_COLLECT_iff const_eq.

	set compr {_} := Singleton.
	obtain Singleton where Singleton_def: {x} = {y. x = y};
		- for thesis if assm;
			apply abbrev[of (x. {y. x = y})];
			- for f if f;
				by assm[of f] #unfold f.
			.
		.
	lemma in_Singleton_iff: x ∈ {y} ⟺ x = y;
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
		by #unfold COLLECT_def in_def COLLECT_in_pair.
end


theory Class:
	import Collect.
	assume COLLECT_ext(cong) (∀x. P.[x] ⟺ Q.[x]) ⟹ {x. P.[x]} = {x. Q.[x]}.
begin
	lemma COLLECT_eq_iff: {x. P.[x]} = {x. Q.[x]} ⟺ (∀x. P.[x] ⟺ Q.[x]);
		apply iff_intro;
		- if eq then for x;
			fold^1 in_COLLECT_iff;
			unfold eq.
		apply COLLECT_ext=.
	obtain (∪) where cup_def: X ∪ Y = {x. x ∈ X ∨ x ∈ Y};
		- for thesis if assm;
			apply abbrev2[of (p. {x. x ∈ fst p ∨ x ∈ snd p})];
			- for f if f;
				by assm[of f] #unfold f.
			.
		.
	lemma in_cup_iff: x ∈ X ∪ Y ⟺ x ∈ X ∨ x ∈ Y;
		unfold cup_def in_COLLECT_iff.

	obtain (`) where image_def: f ` X = {y. ∃x ∈ X. y = f x};
		- for thesis if assm;
			apply abbrev2[of (p. {y. ∃x ∈ snd p. y = fst p x})];
			- for f if f;
				by assm[of f] #unfold f.
			.
		.
	lemma in_image_iff: x ∈ f ` A ⟺ (∃a ∈ A. x = f a);
		unfold image_def in_COLLECT_iff.

	obtain (∩) where cap_def: X ∩ Y = {x. x ∈ X ∧ x ∈ Y};
		- for thesis if assm;
			apply abbrev2[of (p. {x. x ∈ fst p ∧ x ∈ snd p})];
			- for f if f;
				by assm[of f] #unfold f.
			.
		.
	lemma in_cap_iff: x ∈ X ∩ Y ⟺ x ∈ X ∧ x ∈ Y;
		unfold cap_def in_COLLECT_iff.

	set compr {_ ∈ _. _} := COLLECT_in.
	obtain COLLECT_in where COLLECT_in_def: {x ∈ X. P.[x]} = {x. x ∈ X ∧ P.[x]};
		- for thesis if assm;
			apply abbrev2[of (p. fst p ∩ COLLECT (snd p))];
			- for f if f;
				apply assm[of f];
				by #unfold f cap_def in_COLLECT_iff.
			.
		.
	lemma COLLECT_in_cong:
		if X: X = X', P: ∀x. x ∈ X' ⟹ P.[x] ⟺ P'.[x] then {x ∈ X. P.[x]} = {x ∈ X'. P'.[x]};
		by #unfold X P COLLECT_in_def #cong iff.and_cong1.

	obtain class where class_def: class A (⊑) x = {y ∈ A. x ⊑ y};
		- for thesis if assm;
			apply abbrev3[of (p. {y ∈ fst p. fst (snd p) (snd (snd p)) y})];
			- for f if f;
				by assm[of f] #unfold f COLLECT_in_def.
			.
		.
	infix // 110 111 110.
	obtain (//) where quotient_def: A // (⊑) = {C. ∃x ∈ A. C = {y ∈ A. x ⊑ y}};
		- for thesis if assm;
			apply abbrev2[of (p. {C. ∃x ∈ fst p. C = {y ∈ fst p. snd p x y}})];
			- for f if f;
				by assm[of f] #unfold f COLLECT_in_def.
			.
		.
	obtain undefined;.
	obtain (→) where fun_def: A → B = {f. ∀x ∈ A. f x ∈ B};
		- for thesis if assm;
			apply abbrev2[of (p. {f. ∀x ∈ fst p. f x ∈ snd p})];
			- for f if f;
				by assm[of f] #unfold f.
			.
		.
	interpret Fun;
		by #unfold fun_def in_COLLECT_iff ball_iff.
	lemma in_fun_intro: if f: ∀x. x ∈ A ⟹ f x ∈ B then f ∈ A → B;
		by f ball_intro #unfold fun_def in_COLLECT_iff.

	obtain Decided where Decided_def: Decided = {x. x ∨ ¬x};
		- for thesis if assm;
			apply assm[OF eq.refl].
		.

	lemma in_Decided_iff: P ∈ Decided ⟺ P ∨ ¬P;
		unfold Decided_def in_COLLECT_iff.

	lemma in_Decided_cong: if P: P ⟺ P' then P ∈ Decided ⟺ P' ∈ Decided;
		unfold in_Decided_iff P.

	namespace Decided:

		interpret Classical;
			instantiate Prop := Decided.
			note! not_intro and_intro iff_intro.
			note(elim) and_elim iff_elim false_elim.
			note(intro 1) not_elim.
			note(cong) in_Decided_cong.
			interpret imp: Magma Decided (⟹);
				- (⟹) ∈ Decided → Decided → Decided;
					apply in_fun_intro;
					- if x: x ∈ Decided;
						apply in_fun_intro;
						- if y: y ∈ Decided then (x ⟹ y) ∈ Decided;
							unfold in_Decided_iff;
							apply or_elim[OF x[unfolded in_Decided_iff]];
							- if x: x;
								by y[unfolded in_Decided_iff] #unfold imp_imp_iff[OF x].
							-; by or_intro1.
							.
						.
					.
				.
			interpret and: Magma Decided (∧);
				- (∧) ∈ Decided → Decided → Decided;
					apply in_fun_intro;
					- if P: P ∈ Decided;
						apply P[unfolded in_Decided_iff, THEN or_elim];
						- if P1: P;
							apply in_fun_intro;
							- if Q: Q ∈ Decided then (P ∧ Q) ∈ Decided;
								unfold in_Decided_iff;
								apply Q[unfolded in_Decided_iff, THEN or_elim];
								- if Q1: Q; by or_intro1 P1 Q1.
								- if Q0: ¬Q; by or_intro2 nand_intro2[OF Q0].
								.
							.
						- if P0: ¬P;
							by in_fun_intro or_intro2 nand_intro1[OF P0] #unfold in_Decided_iff.
						.
					.
				.
		- true ∈ Decided;
			by #unfold in_Decided_iff.
		- false ∈ Decided;
			by #unfold in_Decided_iff.
		- (⟺) ∈ Decided → Decided → Decided;
			by in_fun_intro and.closed imp.closed #unfold iff_iff_and.
		- (∨) ∈ Decided → Decided → Decided;
			apply in_fun_intro;
			- if P: P ∈ Decided;
				apply P[unfolded in_Decided_iff, THEN or_elim];
				- if P1: P;
					by in_fun_intro #unfold in_Decided_iff iff_true[OF P1].
				- if P0: ¬P;
					apply in_fun_intro;
					- if Q: Q ∈ Decided then (P ∨ Q) ∈ Decided;
						apply Q[unfolded in_Decided_iff, THEN or_elim];
						- if Q1: Q;
							by #unfold in_Decided_iff iff_true[OF Q1].
						- if Q0: ¬Q;
							by or_intro2 P0 Q0 #unfold in_Decided_iff nor_iff.
						.
					.
				.
			.
		- (¬) ∈ Decided → Decided;
			by in_fun_intro or_intro nnot_intro #elim or_elim #unfold in_Decided_iff.
		- P ∈ Decided ⟹ P ∨ ¬ P;
			unfold in_Decided_iff.
		.

	end

	thm Decided.pierce_law.

	lemma nnot_Decided: ¬ ¬ x ∈ Decided;
		unfold in_Decided_iff;
		by nnot_excluded_middle.


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
							-; by or_intro1 P.
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
