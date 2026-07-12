---
## Negation with Free False
---
fix false (¬).
assume not_iff_imp_false#rule ¬P ⟺ (P ⟹ false).

begin

interpret base? TypeFree.FalseNot;
	by #simp not_iff_imp_false.

lemma imp_not_iff_false: if P: P then ¬ P ⟺ false;
	simp not_iff_imp_false iff_true[OF P].

lemma not_cong#cong if PQ: P ⟺ Q then ¬ P ⟺ ¬ Q;
	unfold not_iff_imp_false PQ.

lemma not_false_iff#simp ¬ false ⟺ true;
	by not_false.

lemma not_true_iff#simp ¬ true ⟺ false;
	unfold not_iff_imp_false.

lemma imp_not_commute: (P ⟹ ¬ Q) ⟺ (Q ⟹ ¬ P);
	by iff_intro[OF imp_not_sym imp_not_sym].

lemma nnnot_iff: ¬ ¬ ¬ P ⟺ ¬ P;
	unfold+ not_iff_imp_false;
	by imp3_iff.

lemma nnot_imp_not_iff: (¬ ¬ P ⟹ ¬ Q) ⟺ (P ⟹ ¬ Q);
	unfold imp_not_commute;
	unfold nnnot_iff.

lemma nnimp_not_iff: ¬ ¬ (P ⟹ ¬ Q) ⟺ (P ⟹ ¬ Q);
	apply iff_intro;
	- if nnimp: ¬ ¬ (P ⟹ ¬ Q), P: P then ¬ Q;
		by nnimp_imp_nnot[OF nnimp P, unfold nnnot_iff].
	by nnot_intro.

lemma nnall_not_iff: ¬ ¬ (∀x. ¬ P.[x]) ⟺ (∀x. ¬ P.[x]);
	apply iff_intro;
	- if 1: ¬ ¬ (∀x. ¬ P.[x]);
		by 1[THEN nnall_imp, unfold nnnot_iff].
	by nnot_intro.

