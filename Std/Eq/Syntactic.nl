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

definition BinderApp = dual ((∘) ∘ (∘)) (dual (_AppBind ∘ (|>))).

lemma BinderApp#simp BinderApp op (x. F.[x]) t = op (x. t |> F.[x]);
	simp BinderApp_def.

lemma AllApp_elim1: if 1: BinderApp (∀) (x. F.[x]) t then F.[x] t;
	by 1[simp, of x, simp].

lemma AllApp_intro: if all: ∀x. F.[x] t then BinderApp (∀) (x. F.[x]) t;
	simp;
	- for x; by all.
	.

definition[as and] (∧) = (BinderApp (BinderApp (∀))) (R. dual (dual ∘ ((∘) (⟹) ∘ dual ((∘) ∘ (⟹)) (dual (⟹) R))) R).

instance And;
	- for P Q if P, Q then P ∧ Q;
		simp and_def;
		- for R; simp;
			- if assm; by assm P Q.
			.
		.
	- for P Q if and: P ∧ Q;
		apply and[simp and_def, of P, simp].
	- for P Q if and: P ∧ Q;
		apply and[simp and_def, of Q, simp].
	.


theory LinAbs :=
	import Iff.
	fix _ABS.
	assume _ABS_id#simp (x. _ABS x) = id.
	assume _ABS_const#simp (x. _ABS c) = const c.
	assume _ABS_left#simp (x. _ABS (F.[x] s)) = dual (x. _ABS F.[x]) s.
	assume _ABS_right#simp (x. _ABS (s F.[x])) = s ∘ (x. _ABS F.[x]).
	assume _ABS_eta#simp (x. _ABS (s x)) = s.
	assume _ABS_ext#cong if ∀x. F.[x] = G.[x] then (x. _ABS F.[x]) = (x. _ABS G.[x]).
begin

	set simp (⟺).

	lemma: (x. _ABS (y. _ABS (neg (x = y)))) = (neg ∘) ∘ (=);
		simp.

	lemma: (b. _ABS (x. _ABS (y. _ABS (b (foo (y |>) x))))) = dual ((∘) ∘ (∘)) (dual (foo ∘ (|>)));
		simp.

	lemma: (P. _ABS (Q. _ABS ((P ⟹ Q ⟹ R) ⟹ R))) = dual (dual ∘ (((⟹) ∘) ∘ dual ((∘) ∘ (⟹)) (dual (⟹) R))) R;
		simp.

	lemma: (f. _ABS (x. _ABS (y. _ABS (f (g x y))))) = dual ((∘) ∘ (∘)) g;
		simp.

end

