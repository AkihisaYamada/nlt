---
# Syntactic Safe Combinator
---
import Id, Const, Comp, Dual, BindComb.

begin

theory LinAbs :=-- For computing combinator representation
	import Ext.
	binder ⟨ 0 0.
	prefix ⟩ 0 0.
	fix (⟨) (⟩) _RET _ABS _ABS2 _ABS3 _LREC _RREC _BIND.
	assume _ABS_id#simp (⟨x. ⟩ x) = _RET id.
	assume _ABS_const#simp (⟨ x. ⟩ c) = _RET (const c).
	assume _ABS_RET#simp (⟨x. _RET F.[x]) = (⟨x. ⟩ F.[x]).
	assume _ABS_left#simp (⟨ x. ⟩ F.[x] s) = _LREC (⟨ x. ⟩ F.[x]) s.
	assume _LREC_RET#simp _LREC (_RET s) t = _RET (dual s t).
	assume _ABS_right#simp (⟨ x. ⟩ s F.[x]) = _RREC s (⟨ x. ⟩ F.[x]).
	assume _RREC_RET#simp _RREC s (_RET t) = _RET (s ∘ t).
	assume _ABS_eta#simp (⟨ x. ⟩ s x) = _RET s.
	assume _ABS_bind#simp (⟩ (y. F.[y])) = _ABS (y. F.[y]).
	assume _ABS_triv#simp (⟨ x. _ABS (y. y)) = _RET (y. const y).
	assume _ABS_indep#simp (⟨ x. _ABS (y. F.[x])) = _RET (y. ⟨ x. ⟩ F.[x]).
	assume _ABS_app#simp (_ABS (y. F.[y] G.[y])) = _ABS2 (y. F.[y]) (y. G.[y]).
	assume _ABS2#simp (⟨ x. _ABS2 F.[x] G.[x]) = _ABS3 (⟨ x. ⟩ F.[x]) (⟨ x. ⟩ F.[x]).
	assume _ABS3#simp _ABS3 (_RET f) (_RET g) = _RET (_BindApp f g).
begin

	-- neq
	lemma: (⟨ x y. ⟩ ¬(x = y)) = _RET (((¬) ∘) ∘ (=)).

	lemma: (⟨ f x y. ⟩ f (g x y)) = _RET (dual ((∘) ∘ (∘)) g).

	lemma: (⟨ P Q. ⟩ (P ⟹ Q ⟹ R) ⟹ R) =
			_RET (dual (dual ∘ (((⟹) ∘) ∘ dual ((∘) ∘ (⟹)) (dual (⟹) R))) R);
		simp.

	lemma: (⟨ P Q. ⟩ (∀R. (P ⟹ Q ⟹ R) ⟹ R));
		simp;.

	lemma: (P. _ABS (Q. _ABS ((P ⟹ R) ⟹ (Q ⟹ R) ⟹ R))) =
			dual ((∘) ∘ ((⟹) ∘ dual (⟹) R)) (dual ((⟹) ∘ dual (⟹) R) R);
		simp.

end

definition app = (id ∘).

lemma app#simp app f x = f x;
	simp app_def.

definition paracomp = dual ((∘) ∘ dual (∘)).

lemma paracomp_app#simp paracomp f g x y = f x (g y); by #simp paracomp_def.

definition[as revapp] (|>) = dual id.

lemma revapp#simp x |> f = f x; by #simp revapp_def.

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
	- for x y; apply pair_tp_spec[OF pair_def fst_def snd_def].
	- for x y; apply pair_tp_spec[OF pair_def fst_def snd_def].
	.

definition uncurry = dual ((∘) ∘ (∘)) (,).

lemma uncurry#simp uncurry f x y = f (x,y);
	simp uncurry_def.

definition pair_assoc = dual ((∘) ∘ (∘) ∘ (,)) (,).

lemma pair_assoc#simp pair_assoc x y z = (x,y,z);
	simp pair_assoc_def.

context LinAbs begin
	-- deriving _BinderApp
	lemma: (op. _ABS (F. _ABS (G. _ABS (op (_BinderApp F G))))) = dual ((∘) ∘ (∘)) _BinderApp;
		simp.
end

definition _BinderApp = dual ((∘) ∘ (∘)) _BindApp.

lemma _BinderApp#simp _BinderApp op (x. F.[x]) (x. G.[x]) = op (x. F.[x] G.[x]);
	simp _BinderApp_def.


context LinAbs begin

	-- deriving existence
	lemma: (P. _ABS (P ⟹ R)) = (R ⟸);
		simp _if_def.
	lemma: (P. _ABS ((∀x. P.[x] ⟹ R) ⟹ R)) = dual ((⟹) ∘ (AppBinder (∀) (R ⟸) ∘ id)) R;
		have 1: (∀x. P.[x] ⟹ R) = AppBinder (∀) (R ⟸) (x. P.[x]);
			simp.
		unfold 1;
		simp.

	lemma: (P. _ABS (∀x. x ∈ A ⟹ P.[x])) = (∀) ∘ (P. _ABS (x. x ∈ A ⟹ P.[x])).

	lemma: (x. (P. _ABS (x ∈ A ⟹ P.[x]))) = (x. (x ∈ A ⟹) ∘); simp;


end

definition BinderApp = dual ((∘) ∘ (∘)) (dual (_AppBind ∘ (|>))).

lemma BinderApp#simp BinderApp op (x. F.[x]) t = op (x. t |> F.[x]);
	simp BinderApp_def.

definition false = (∀P. P).

definition[as not] (¬) = (false ⟸).

lemma not_eq: (¬P) = (P ⟹ false); by #simp not_def.

instance IntuitionisticNot;
	retain false; by #simp false_def.
	by #simp not_def.

definition[as neq] (≠) = ((¬) ∘) ∘ (=).

lemma neq_eq: (x ≠ y) = (¬(x = y)); by #simp neq_def.

definition[as and] (∧) =
	(BinderApp (BinderApp (∀))) (R. dual (dual ∘ ((⟹) ∘) ∘ dual ((∘) ∘ (⟹)) (R ⟸)) R).

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
	BinderApp (∀) (R. dual ((⟹) ∘ AppBinder (∀) (R ⟸)) R).

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


