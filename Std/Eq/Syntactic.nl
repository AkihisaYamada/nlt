---
# Syntactic Safe Combinator
---
import Id, Const, Comp, Dual, AppBind.

begin

definition app = (∘) id.

lemma app#simp app f x = f x;
	simp app_def.

definition paracomp = dual ((∘) ∘ dual (∘)).

lemma paracomp_app#simp paracomp f g x y = f x (g y);
	simp paracomp_def.

definition[as revapp] (|>) = dual id.

lemma revapp#simp x |> f = f x;
	simp revapp_def.

lemma : ((z |>) ∘ (y |>) ∘ (x |>)) f = f x y z.

obtain pair_tp where pair_tp_spec:
	if	pair = pair_tp (const ∘ dual const),
		fst = pair_tp (const const),
		snd = pair_tp (const ∘ const),
		(∀x y. fst (pair x y) = x) ⟹
		(∀x y. snd (pair x y) = y) ⟹ P
	then P;
	- for thesis if assm;
		apply assm[of ((dual ((∘) ∘ dual ∘ dual id) id |>) ∘ ((const |>) |>) ∘ ((dual const |>) |>))];
		- for pair if pair0 for fst if fst0 for snd if snd0 for P if assm2;
			apply assm2;
			- for x y; simp fst0 pair0.
			- for x y; simp snd0 pair0.
			.
		.
	.

definition[as pair] (,) = pair_tp (const ∘ dual const).
definition fst = pair_tp (const const).
definition snd = pair_tp (const ∘ const).

instance Pair;
	- for x y;
		apply pair_tp_spec[OF pair_def fst_def snd_def].
	- for x y;
		apply pair_tp_spec[OF pair_def fst_def snd_def].
	.

definition uncurry = dual ((∘) ∘ (∘)) (,).

lemma uncurry#simp uncurry f x y = f (x,y);
	simp uncurry_def.

definition pair_assoc = dual ((∘) ∘ ((∘) ∘ (,))) (,).

lemma pair_assoc#simp pair_assoc x y z = (x,y,z);
	simp pair_assoc_def.

definition AppBinder = dual ((∘) ∘ (∘)) _AppBind.

lemma AppBinder#simp AppBinder op f (x. G.[x]) = op (x. f G.[x]);
	simp AppBinder_def.

definition BinderApp = dual ((∘) ∘ (∘)) (dual (_AppBind ∘ (|>))).

lemma BinderApp#simp BinderApp op (x. F.[x]) t = op (x. t |> F.[x]);
	simp BinderApp_def.

definition false = (∀P. P).

definition[as not] (¬) = (false ⟸).

instance IntuitionisticNot;
	retain false; by #simp false_def.
	by #simp not_def.

definition[as neq] (≠) = ((¬) ∘) ∘ (=).

lemma neq_eq: (x ≠ y) = (¬(x = y));
	by #simp neq_def.

definition[as and] (∧) =
	(BinderApp (BinderApp (∀))) (R. dual (dual ∘ ((⟹) ∘) ∘ dual ((∘) ∘ (⟹)) (R ⟸)) R).

instance And;
	- if [P, Q] then P ∧ Q;
		simp and_def;
		- for R; simp;
			- if assm; by assm.
			.
		.
	- if and: P ∧ Q;
		apply and[simp and_def, of P, simp].
	- if and: P ∧ Q;
		apply and[simp and_def, of Q, simp].
	.

definition[as or] (∨) =
	(BinderApp (BinderApp (∀))) (R. dual ((∘) ∘ (⟹) ∘ (R ⟸)) (dual ((⟹) ∘ (R ⟸)) R)).

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
	BinderApp (∀) (R. dual ((⟹) ∘ (AppBinder (∀) (R ⟸))) R).

instance Ex;
	- for s if Ps: P.[s] then ∃x. P.[x];
		simp ex_def;
		- for Q; simp;
			- if assm;
				by assm[of s, simp] Ps.
			.
		.
	- if ex: ∃x. P.[x], assm: ∀x. P.[x] ⟹ Q then Q;
		apply ex[simp ex_def, of Q, simp];
		- for x; simp;
			- if Px: P.[x];
				by assm[OF Px].
			.
		.
	.

theory LinAbs :=
	import Ext.
	fix _ABS.
	assume _ABS_id#simp (x. _ABS x) = id.
	assume _ABS_id_unbind#simp (F. _ABS (x. F.[x])) = id.
	assume _ABS_const#simp (x. _ABS c) = const c.
	assume _ABS_left#simp (x. _ABS (F.[x] s)) = dual (x. _ABS F.[x]) s.
	assume _ABS_right#simp (x. _ABS (s F.[x])) = s ∘ (x. _ABS F.[x]).
	assume _ABS_eta#simp (x. _ABS (s x)) = s.
	assume _ABS_ext#cong if ∀x. F.[x] = G.[x] then (x. _ABS F.[x]) = (x. _ABS G.[x]).
begin

	-- neq
	lemma: (x. _ABS (y. _ABS (¬(x = y)))) = ((¬) ∘) ∘ (=);
		simp.

	lemma: (b. _ABS (x. _ABS (y. _ABS (b (foo (y |>) x))))) = dual ((∘) ∘ (∘)) (dual (foo ∘ (|>)));
		simp.

	lemma: (f. _ABS (x. _ABS (y. _ABS (f (g x y))))) = dual ((∘) ∘ (∘)) g;
		simp.

	lemma: (P. _ABS (Q. _ABS ((P ⟹ Q ⟹ R) ⟹ R))) =
			dual (dual ∘ (((⟹) ∘) ∘ dual ((∘) ∘ (⟹)) (dual (⟹) R))) R;
		simp.

	lemma: (P. _ABS (Q. _ABS ((P ⟹ R) ⟹ (Q ⟹ R) ⟹ R))) =
			dual ((∘) ∘ ((⟹) ∘ dual (⟹) R)) (dual ((⟹) ∘ dual (⟹) R) R);
		simp.

	-- deriving AppBinder
	lemma: (op. _ABS (f. _ABS (G. _ABS (op (_AppBind f G))))) = dual ((∘) ∘ (∘)) _AppBind;
		simp.

	-- deriving existence
	lemma: (P. _ABS (P ⟹ R)) = (R ⟸);
		simp _if_def.
	lemma: (P. _ABS ((∀x. P.[x] ⟹ R) ⟹ R)) = dual ((⟹) ∘ (AppBinder (∀) (R ⟸) ∘ id)) R;
		have 1: (∀x. P.[x] ⟹ R) = AppBinder (∀) (R ⟸) (x. P.[x]);
			simp.
		unfold 1;
		simp.



end

