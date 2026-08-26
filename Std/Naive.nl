---
# Naive Logic
---

import Iff, Eq, Syntactic.

begin

---
## Defining Type-Free Logical Operators

We can derive intuitionistic logic operators, except for `(⟺)`.
---
definition false = (∀P. P).

definition[as not] (¬) = (false ⟸).

lemma not_eq: (¬P) = (P ⟹ false); by #simp not_def.

instance IntuitionisticNot;
	retain false; by #simp false_def.
	by #simp not_def.

definition[as neq] (≠) = ((¬) ∘) ∘ (=).

lemma neq_eq: (x ≠ y) = (¬(x = y)); by #simp neq_def.

definition[as and] (∧) =
	_BinderApp ( _BinderApp (∀)) (R. dual (dual ∘ (((⟹) ∘) ∘ dual ((∘) ∘ (⟹)) (dual (⟹) R))) R).

instance And;
	- if [P, Q] then P ∧ Q;
		simp and_def;
		- for R; simp;
			- if assm; by assm.
			.
		.
	- if and: P ∧ Q; apply and[simp and_def, of P, simp].
	- if and: P ∧ Q; apply and[simp and_def, of Q, simp].
	.

definition[as or] (∨) =
	_BinderApp ( _BinderApp (∀)) (R. dual ((∘) ∘ ((⟹) ∘ dual (⟹) R)) (dual ((⟹) ∘ dual (⟹) R) R)).

instance Or;
	- if P: P then P ∨ Q;
		simp or_def;
		- for R; simp;
			- if PR, QR; by PR P.
			.
		.
	- if Q: Q then P ∨ Q;
		simp or_def;
		- for R; simp;
			- if PR, QR; by QR Q.
			.
		.
	- if or: P ∨ Q for R;
		apply or[simp or_def, of R, simp]>0.
	.

definition[as ex] (∃) =
	_BinderApp (∀) (Q. dual ((⟹) ∘ ((∀) ∘ dual ( _BindAppBind ∘ _BindAppBind (y. (⟹))) (y. Q))) Q).

instance Ex;
	- for s if Ps: P.[s] then ∃x. P.[x];
		simp ex_def;
		- for Q; simp;
			- if assm;
				by assm[of s] Ps.
			.
		.
	- if ex: ∃x. P.[x], assm: ∀x. P.[x] ⟹ Q then Q;
		apply ex[simp ex_def, of Q, simp];
		- for x;
			- if Px: P.[x];
				by assm[OF Px].
			.
		.
	.

---
## Restricted Quantifiers
---

definition all_rel = (((∀) ∘) ∘) ∘ _BinderApp ( _BinderApp _BindAppBind) (y. ((⟹) ∘) ∘ dual id y).

lemma all_rel_intro: if assm: ∀x. x ⊏ a ⟹ P.[x] then all_rel (⊏) a (x. P.[x]);
	simp all_rel_def;
	- for x; simp; by assm.
	.

lemma all_rel_elim1: if all: all_rel (⊏) a (x. P.[x]), x: x ⊏ a then P.[x];
	by all[simp all_rel_def, of x, simp, OF x].

definition ex_rel = (((∃) ∘) ∘) ∘ _BinderApp ( _BinderApp _BindAppBind) (y. ((∧) ∘) ∘ dual id y).

lemma ex_rel_intro1: if x: x ⊏ a, Px: P.[x] then ex_rel (⊏) a (x. P.[x]);
	simp ex_rel_def;
	apply ex_intro1[of x]; by x Px.

lemma ex_rel_elim: if ex: ex_rel (⊏) a (x. P.[x]), assm: ∀x. x ⊏ a ⟹ P.[x] ⟹ Q then Q;
	apply ex[simp ex_rel_def, THEN ex_elim];
	- for x if assm2;
		use assm2[simp]; by assm[of x].
	.


