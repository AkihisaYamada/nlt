---
# Syntactic Safe Combinator
---
import Id, Const, Comp, Dual, BindComb.

begin

definition app = (id ∘).

lemma app#simp app f x = f x;
	simp app_def.

definition _BindApp = (dual ((∘) ∘ _BindAppBind) _BindConst).

lemma _BindApp#simp _BindApp (x. F.[x]) s = (x. F.[x] s); by #simp _BindApp_def.

definition _AppBind = _BindAppBind ∘ _BindConst.

lemma _AppBind#simp _AppBind f (x. F.[x]) = (x. f F.[x]); by #simp _AppBind_def.

definition _BinderApp = dual ((∘) ∘ (∘)) _BindApp.

lemma _BinderApp#simp _BinderApp op (x. F.[x]) s = op (x. F.[x] s);
	by #simp _BinderApp_def.

definition _BindApp2 = (_BindApp ∘) ∘ _BindAppBind.

lemma _BindApp2#simp _BindApp2 (x. F.[x]) (x. G.[x]) s = (x. F.[x] G.[x] s);
	by #simp _BindApp2_def.

definition _BindAppLeft = dual ∘ ((_BindAppBind ∘) ∘ _BindApp).

lemma _BindAppLeft#simp _BindAppLeft (x. F.[x]) (x. G.[x]) s = (x. F.[x] s G.[x]);
	by #simp _BindAppLeft_def.

definition _BindAppRight = dual ((∘) ∘ ((∘) ∘ _BindAppBind)) _BindApp.

lemma _BindAppRight#simp _BindAppRight (x. F.[x]) (x. G.[x]) s = (x. F.[x] (G.[x] s));
	by #simp _BindAppRight_def.

theory LinAbs :=-- For computing combinator representation
	import Ext.
	binder ⟨ 0 0.
	prefix ⟩ 0 0.
	prefix ⟩' -10 0.
	prefix ⟩'' 0 0.
	fix (⟨) (⟩) (⟩') (⟩'') _RET _LREC _RREC _LREC' _RREC' _RET' _RET'' _RIP.
	assume _ABS_id#simp (⟨ x. ⟩ x) = _RET id.
	assume _ABS_const#simp (⟨ x. ⟩ c) = _RET (const c).
	assume _ABS_RET#simp (⟨ x. _RET F.[x]) = (⟨x. ⟩ F.[x]).
	assume _ABS_left#simp (⟨ x. ⟩ F.[x] s) = _LREC (⟨ x. ⟩ F.[x]) s.
	assume _LREC_RET#simp _LREC (_RET s) t = _RET (dual s t).
	assume _ABS_right#simp (⟨ x. ⟩ s F.[x]) = _RREC s (⟨ x. ⟩ F.[x]).
	assume _RREC_RET#simp _RREC f (_RET g) = _RET (f ∘ g).
	assume _RREC_RET'#simp _RREC s (_RET' (y. F.[y])) = _RET (_BinderApp s (y. F.[y])).
	assume _RREC_RET''#simp _RREC f (_RET'' g) = _RET (f ∘ g).
	assume _ABS_eta#simp (⟨ x. ⟩ s x) = _RET s.
	assume _ABS_bind#simp (⟩ (y. F.[y])) = (⟩' y. F.[y]).
	assume _ABS'_const#simp (⟨ x. ⟩' y. F.[y]) = _RET' (y. const F.[y]).
	assume _ABS'_id#simp (⟨ x. ⟩' y. x) = _RET' (y. id).
	assume _ABS'_BIND#simp (⟨ P. ⟩' y. P.[y]) = _RET'' id.
	assume _ABS'_app#simp (⟩' y. F.[y] G.[y]) = (⟩'' (y. F.[y]) (y. G.[y])).
	assume _ABS'2_left#simp (⟨ x. ⟩'' (F.[x]) s) = _LREC' (⟨ x. ⟩' F.[x]) s.
	assume _ABS'2_right#simp (⟨ x. ⟩'' s (F.[x])) = _RREC' s (⟨ x. ⟩' F.[x]).
	assume _LREC'#simp _LREC' (_RET' (y. F.[y])) (y. G.[y]) = _RET' (y. dual F.[y] G.[y]).
	assume _RREC'#simp _RREC' (y. F.[y]) (_RET' (y. G.[y])) = _RET' (y. F.[y] ∘ G.[y]).
	assume _RREC'_eta#simp _RREC' (y. F.[y]) (_RET' (y. id)) = _RET' (y. F.[y]).
	assume _RREC'_BIND#simp _RREC' f (_RET'' g) = _RET'' (_BindAppBind f ∘ g).
	assume _RIP#simp _RIP (_RET s) = s. 
begin

	-- _BindApp
	lemma: _RIP (⟨ x y. ⟩ _BindAppBind x ( _BindConst y)) = dual ((∘) ∘ _BindAppBind) _BindConst.

	-- _AppBind
	lemma: _RIP (⟨ x y. ⟩ _BindAppBind ( _BindConst x) y) = _BindAppBind ∘ _BindConst.

	-- _BindAppLeft
	lemma: _RIP (⟨ x y z. ⟩ _BindAppBind (_BindApp x z) y) = dual ∘ ((_BindAppBind ∘) ∘ _BindApp).

	-- _BindAppRight
	lemma: _RIP (⟨ x y z. ⟩ _BindAppBind x (_BindApp y z)) = dual ((∘) ∘ ((∘) ∘ _BindAppBind)) _BindApp.

	-- neq
	lemma: _RIP (⟨ x y. ⟩ ¬(x = y)) = ((¬) ∘) ∘ (=).

	lemma: _RIP (⟨ f x y. ⟩ f (g x y)) = dual ((∘) ∘ (∘)) g.

	-- and
	lemma: _RIP (⟨ P Q. ⟩ ∀R. (P ⟹ Q ⟹ R) ⟹ R) =
			_BinderApp (_BinderApp (∀)) (y. dual (dual ∘ (((⟹) ∘) ∘ dual ((∘) ∘ (⟹)) (dual (⟹) y))) y);
		simp[at 0].

	-- or
	lemma: _RIP (⟨ P Q. ⟩ ∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R) =
		_BinderApp (_BinderApp (∀)) (y. dual ((∘) ∘ ((⟹) ∘ dual (⟹) y)) (dual ((⟹) ∘ dual (⟹) y) y));
		simp[at 0].

	-- ex
	lemma: _RIP (⟨ P. ⟩ ∀ Q. (∀ x. P.[x] ⟹ Q) ⟹ Q);
		simp[repeat 8];

	-- restricted all
	lemma: (⟨ A P. ⟩ (∀x. x : A ⟹ P.[x])) =
		_RET (((∀) ∘) ∘ dual ((∘) ∘ _BinderApp _BindAppBind (y. (⟹) ∘ (y :))) id).
end

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


definition false = (∀P. P).

definition[as not] (¬) = (false ⟸).

lemma not_eq: (¬P) = (P ⟹ false); by #simp not_def.

instance IntuitionisticNot;
	retain false; by #simp false_def.
	by #simp not_def.

definition[as neq] (≠) = ((¬) ∘) ∘ (=).

lemma neq_eq: (x ≠ y) = (¬(x = y)); by #simp neq_def.

definition[as and] (∧) =
	_BinderApp (_BinderApp (∀)) (R. dual (dual ∘ (((⟹) ∘) ∘ dual ((∘) ∘ (⟹)) (dual (⟹) R))) R).

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
	_BinderApp (_BinderApp (∀)) (R. dual ((∘) ∘ ((⟹) ∘ dual (⟹) R)) (dual ((⟹) ∘ dual (⟹) R) R)).

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
	_BinderApp (∀) (R. dual ((⟹) ∘ AppBinder (∀) (R ⟸)) R).

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

extend Membership begin

	definition[as ball] (∀∈) = ((∀) ∘) ∘ dual ((∘) ∘ _BinderApp _BindAppBind (y. (⟹) ∘ (y ∈))) id.

	instance AllIn;


end
