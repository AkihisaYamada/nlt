---
# Derived Classical Propositional Logic

The collection of *decided* terms form classical propositional logic.
---
import Collection.

obtain Decided where Decided_def: Decided = {x. x ∨ ¬x};
	- for thesis if assm;
		apply assm[OF eq.refl].
	.

lemma in_Decided_iff: P ∈ Decided ⟺ P ∨ ¬P;
	unfold Decided_def in_Collect_iff.

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
			- for P Q if P: P ∈ Decided, Q: Q ∈ Decided then (P ⟹ Q) ∈ Decided;
				unfold in_Decided_iff;
				apply or_elim[OF P[unfolded in_Decided_iff]];
				- if P: P;
					by Q[unfolded in_Decided_iff] #unfold imp_imp_iff[OF P].
				-; by or_intro1.
				.
			.
		interpret and: Magma Decided (∧);
			- for P Q if P: P ∈ Decided, Q: Q ∈ Decided then (P ∧ Q) ∈ Decided;
				apply P[unfolded in_Decided_iff, THEN or_elim];
				- if P1: P;
					unfold in_Decided_iff;
					apply Q[unfolded in_Decided_iff, THEN or_elim];
					- if Q1: Q; by or_intro1 P1 Q1.
					- if Q0: ¬Q; by or_intro2 nand_intro2[OF Q0].
					.
				- if P0: ¬P;
					by in_fun_intro or_intro2 nand_intro1[OF P0] #unfold in_Decided_iff.
				.
			.
		- then true ∈ Decided;
			by #unfold in_Decided_iff.
		- then false ∈ Decided;
			by #unfold in_Decided_iff.
		- for P Q if ! P ∈ Decided, ! Q ∈ Decided then (P ⟺ Q) ∈ Decided;
			by in_fun_intro and.closed imp.closed #unfold iff_iff_and.
		- for P Q if P: P ∈ Decided, Q: Q ∈ Decided then (P ∨ Q) ∈ Decided;
			apply P[unfolded in_Decided_iff, THEN or_elim];
			- if P1: P;
				by in_fun_intro #unfold in_Decided_iff iff_true[OF P1].
			- if P0: ¬P;
				apply Q[unfolded in_Decided_iff, THEN or_elim];
				- if Q1: Q;
					by #unfold in_Decided_iff iff_true[OF Q1].
				- if Q0: ¬Q;
					by or_intro2 P0 Q0 #unfold in_Decided_iff nor_iff.
				.
			.
		- then P ∈ Decided ⟹ (¬ P) ∈ Decided;
			by or_intro nnot_intro #elim or_elim #unfold in_Decided_iff.
		- then P ∈ Decided ⟹ P ∨ ¬ P;
			unfold in_Decided_iff.
		.
	end
end

lemma nnot_Decided: ¬ ¬ x ∈ Decided;
	unfold in_Decided_iff;
	by nnot_excluded_middle.
