---
# Two-Valuedness Assumption
---
assume imp_imp_eq: if P, Q then P = Q.
assume imp_eq: if P then (P ⟹ Q) = Q.

begin

instance True.

lemma eq_true: if P: P then P = true;
	by imp_imp_eq[OF P true_intro].

lemma true_eq: if P: P then true = P;
	unfold eq_true[OF P].

lemma eq_refl_eq_true: (x = x) = true;
	by eq_true.

lemma weaken_eq: (P ⟹ Q ⟹ P) = true;
	by eq_true.

lemma imp_true_eq: (P ⟹ true) = true;
	by eq_true true_intro.

lemma true_imp_eq: (true ⟹ P) = P;
	by imp_eq[OF true_intro].
