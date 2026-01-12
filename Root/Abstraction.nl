---
# Logic on Binary Abstraction
---
import Eq.
import Pair.
assume abst_pair: if ∀f. (∀x y. f x y = F.[(x,y)]) ⟹ P then P.

begin

--- This allows unary and multi-ary abstractions. ---
interpret UnaryAbstraction;
	- for F P if assm;
		note(cong) eq.cong_meta[of F].
		apply abst_pair[of (p. F.[snd p])];
		- for f if f;
			by assm[of (f fst)] #unfold f snd.
		.
	.
lemma abst_triple: if assm: ∀f. (∀x y z. f x y z = F.[(x,y,z)]) ⟹ P then P;
	note(cong) eq.cong_meta[of F].
	apply abst_pair[of (t. F.[(fst (fst t), snd (fst t), snd t)])];
	- for f2 if f2;
		apply abst_pair[of (p. f2 p)];
		- for f3 if f3;
			by assm[of f3] #unfold f3 f2 fst snd.
		.
	.
--- One can obtain type-free binary logical operators by abstraction. ---
interpret Iff;
	obtain (⟺) where
		iff_intro: (P ⟹ Q) ⟹ (Q ⟹ P) ⟹ (P ⟺ Q),
		iff_elim1: (P ⟺ Q) ⟹ P ⟹ Q,
		iff_elim2: (P ⟺ Q) ⟹ Q ⟹ P;
		- for thesis if assm;
			apply abst_pair[of (p. ∀R. ((fst p ⟹ snd p) ⟹ (snd p ⟹ fst p) ⟹ R) ⟹ R)];
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
	note(cong) eq_imp_iff.
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
			apply abst_pair[of (p. ∀R. (fst p ⟹ snd p ⟹ R) ⟹ R)];
			- for f if f;
				apply assm[of f, unfolded f fst snd].
			.
		.
	obtain (∨) where
		or_intro1: ∀P Q. P ⟹ P ∨ Q,
		or_intro2: ∀P Q. Q ⟹ P ∨ Q,
		or_elim: P ∨ Q ⟹ ∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R;
		- for thesis if assm;
			apply abst_pair[of (p. ∀R. (fst p ⟹ R) ⟹ (snd p ⟹ R) ⟹ R)];
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
			apply abst[of (P. P ⟹ false)];
			- for f if f;
				apply assm[of f, unfolded f].
			.
		.
	.
note(cong) eq_imp_iff.
interpret Const;
	obtain const where const_eq: const x y = x;
		- for thesis if elim;
			apply abst_pair[of (p. fst p)];
			- for f if f;
				by elim[of f] #unfold f fst.
			.
		.
	.
lemma curry: for f, ∃f'. ∀x y. f' x y = f (x,y);
	apply abst_pair[of (p. f p)];
	- for f' if f';
		by ex_intro1[of f'] #unfold f' fst snd.
	.
obtain inverts where
	inverts_intro: (∀x. f (g x) = x) ⟹ inverts f g,
	inverts_elim1: inverts f g ⟹ ∀x. f (g x) = x;
	- for thesis if assm;
		apply abst_pair[of (p. ∀x. fst p (snd p x) = x)];
		- for inverts if inverts;
			apply assm[of inverts, unfolded inverts fst snd].
		.
	.
obtain rev_app where rev_app: rev_app x f = f x;
	- for thesis;
		apply abst_pair[of (p. snd p (fst p)), unfolded fst snd]=.
	.

interpret Collect;
	obtain Collect_in_pair where
		Collect_in_pair: snd Collect_in_pair x (fst Collect_in_pair P) ⟺ P x;
		- for thesis if assm;
			apply assm[of (id,rev_app)];
			by #unfold fst snd rev_app.
		.
	obtain Collect where Collect_def: Collect = fst Collect_in_pair;
		- for thesis if assm;
			apply assm[OF eq.refl].
		.
	obtain (∈) where in_def: (∈) = snd Collect_in_pair;
		- for thesis if assm;
			apply assm[OF eq.refl].
		.
	by #unfold Collect_def in_def Collect_in_pair.

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
				apply abst_triple[of (t. THE z. fst t ∧ z = fst (snd t) ∨ (fst t ⟹ fst (snd t) = snd (snd t)) ∧ z = snd (snd t))];
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
