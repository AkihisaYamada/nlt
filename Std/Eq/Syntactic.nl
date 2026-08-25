---
# Syntactic Safe Combinator
---
import Std.Syntactic.

begin

instance Id;
	by id_intro[for z, of (x. x = z)].

instance Const;
	by const_intro[for z, of (x. x = z)].

instance Comp;
	by o_intro[for z, of (x. x = z)].

instance Dual;
	by dual_intro[for z, of (x. x = z)].

instance BindComb;
	- by _BindAppBind_intro[for z, of (x. x = z)].
	- by _BindConst_intro[for z, of (x. x = z)].
	.

---
## Helper Combinators
---

definition app = (id ∘).

lemma app#simp app f x = f x; by #simp app_def.

-- Reverse application yields Church encoding of pairs.

definition[as revapp] (|>) = dual id.

lemma revapp#simp x |> f = f x; by #simp revapp_def.

lemma : ((z |>) ∘ (y |>) ∘ (x |>)) f = f x y z.

definition paracomp = dual ((∘) ∘ dual (∘)).

lemma paracomp_app#simp paracomp f g x y = f x (g y); by #simp paracomp_def.


definition _BindApp = (dual ((∘) ∘ _BindAppBind) _BindConst).

lemma _BindApp#simp _BindApp (x. F.[x]) s = (x. F.[x] s); by #simp _BindApp_def.

definition _AppBind = _BindAppBind ∘ _BindConst.

lemma _AppBind#simp _AppBind f (x. F.[x]) = (x. f F.[x]); by #simp _AppBind_def.

definition _BinderApp = dual ((∘) ∘ (∘)) _BindApp.

lemma _BinderApp#simp _BinderApp op (x. F.[x]) s = op (x. F.[x] s);
	by #simp _BinderApp_def.

definition _BindApp2 = ( _BindApp ∘) ∘ _BindAppBind.

lemma _BindApp2#simp _BindApp2 (x. F.[x]) (x. G.[x]) s = (x. F.[x] G.[x] s);
	by #simp _BindApp2_def.

definition _BindAppLeft = dual ∘ (( _BindAppBind ∘) ∘ _BindApp).

lemma _BindAppLeft#simp _BindAppLeft (x. F.[x]) (x. G.[x]) s = (x. F.[x] s G.[x]);
	by #simp _BindAppLeft_def.

definition _BindAppRight = dual ((∘) ∘ ((∘) ∘ _BindAppBind)) _BindApp.

lemma _BindAppRight#simp _BindAppRight (x. F.[x]) (x. G.[x]) s = (x. F.[x] (G.[x] s));
	by #simp _BindAppRight_def.

theory LinAbs :=-- For computing combinator representation
	import MetaExt.
	binder ⟨ 0 0.
	prefix ⟩ 0 0.
	prefix ⟩' -10 0.
	prefix ⟩'' 0 0.
	fix (⟨) (⟩) (⟩') (⟩'') _RET _LREC _RREC _LREC' _RREC' _RET' _RET'' _RIP.
	assume _ABS_id#simp (⟨ x. ⟩ x) = _RET id.
	assume _ABS_const#simp (⟨ x. ⟩ c) = _RET (const c).
	assume _ABS_RET#simp (⟨ x. _RET F.[x]) = (⟨x. ⟩ F.[x]).
	assume _ABS_left#simp (⟨ x. ⟩ F.[x] s) = _LREC (⟨ x. ⟩ F.[x]) s.
	assume _LREC_RET#simp _LREC ( _RET f) s = _RET (dual f s).
	assume _ABS_right#simp (⟨ x. ⟩ s F.[x]) = _RREC s (⟨ x. ⟩ F.[x]).
	assume _RREC_RET#simp _RREC f ( _RET g) = _RET (f ∘ g).
	assume _RREC_RET'#simp _RREC s ( _RET' (y. F.[y])) = _RET ( _BinderApp s (y. F.[y])).
	assume _ABS_eta#simp (⟨ x. ⟩ s x) = _RET s.
	assume _ABS_bind#simp (⟩ (y. F.[y])) = (⟩' y. F.[y]).
	assume _ABS'_const#simp (⟨ x. ⟩' y. F.[y]) = _RET' (y. const F.[y]).
	assume _ABS'_id#simp (⟨ x. ⟩' y. x) = _RET' (y. id).
	assume _ABS'_BIND#simp (⟨ P. ⟩' y. P.[y]) = _RET id.
	assume _ABS'_app#simp (⟩' y. F.[y] G.[y]) = (⟩'' (y. F.[y]) (y. G.[y])).
	assume _ABS'_2_left #simp (⟨ x. ⟩'' (F.[x]) s) = _LREC' (⟨ x. ⟩' F.[x]) s.
	assume _ABS'_2_right#simp (⟨ x. ⟩'' s (F.[x])) = _RREC' s (⟨ x. ⟩' F.[x]).
	assume _LREC'_RET'#simp _LREC' ( _RET' (y. F.[y])) (y. G.[y]) = _RET' (y. dual F.[y] G.[y]).
	assume _LREC'_RET #simp _LREC' ( _RET f) (y. G.[y]) = _RET (dual ( _BindAppBind ∘ f) (y. G.[y])).
	assume _RREC'_RET'#simp _RREC' (y. F.[y]) ( _RET' (y. G.[y])) = _RET' (y. F.[y] ∘ G.[y]).
	assume _RREC'_RET #simp _RREC' (y. F.[y]) ( _RET g) = _RET ( _BindAppBind (y. F.[y]) ∘ g).
	assume _RREC'_eta'#simp _RREC' (y. F.[y]) ( _RET' (y. id)) = _RET' (y. F.[y]).
	assume _RREC'_eta #simp _RREC' (y. F.[y]) ( _RET id) = _RET ( _BindAppBind (y. F.[y])).
	assume _RIP#simp _RIP ( _RET s) = s. 
begin
	-- for _LREC'_RET
	lemma: _RIP (⟨ x. ⟩ _BindAppBind (f x) g) = dual ( _BindAppBind ∘ f) g.

	-- _BindApp
	lemma: _RIP (⟨ x y. ⟩ _BindAppBind x ( _BindConst y)) = dual ((∘) ∘ _BindAppBind) _BindConst.

	-- _AppBind
	lemma: _RIP (⟨ x y. ⟩ _BindAppBind ( _BindConst x) y) = _BindAppBind ∘ _BindConst.

	-- _BindAppLeft
	lemma: _RIP (⟨ x y z. ⟩ _BindAppBind ( _BindApp x z) y) = dual ∘ (( _BindAppBind ∘) ∘ _BindApp).

	-- _BindAppRight
	lemma: _RIP (⟨ x y z. ⟩ _BindAppBind x ( _BindApp y z)) = dual ((∘) ∘ ((∘) ∘ _BindAppBind)) _BindApp.

	-- neq
	lemma: _RIP (⟨ x y. ⟩ ¬(x = y)) = ((¬) ∘) ∘ (=).

	lemma: _RIP (⟨ f x y. ⟩ f (g x y)) = dual ((∘) ∘ (∘)) g.

	-- and
	lemma: _RIP (⟨ P Q. ⟩ ∀R. (P ⟹ Q ⟹ R) ⟹ R) =
			_BinderApp ( _BinderApp (∀)) (y. dual (dual ∘ (((⟹) ∘) ∘ dual ((∘) ∘ (⟹)) (dual (⟹) y))) y);
		simp[at 0].

	-- or
	lemma: _RIP (⟨ P Q. ⟩ ∀R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R) =
		_BinderApp ( _BinderApp (∀)) (y. dual ((∘) ∘ ((⟹) ∘ dual (⟹) y)) (dual ((⟹) ∘ dual (⟹) y) y));
		simp[at 0].

	-- ex
	lemma: _RIP (⟨ P. ⟩ (∀ x. P.[x] ⟹ Q) ⟹ Q) = dual ((⟹) ∘ ((∀) ∘ dual ( _BindAppBind ∘ _BindAppBind (y. (⟹))) (y. Q))) Q.

	-- restricted quantifiers
	lemma: _RIP (⟨ (⊏) a P. ⟩ (∀x. x ⊏ a ⟹ P.[x])) =
		(((∀) ∘) ∘) ∘ _BinderApp ( _BinderApp _BindAppBind) (y. ((⟹) ∘) ∘ dual id y).

	lemma: _RIP (⟨ i t e. ⟩ f t e i) = dual (dual ∘ f).
end

---
## Instantiating Pairs

We can already encode pairs by combinators, but letting pairs behave as functions can be confusing.
So we abstract the encoding by obtaining the pair constructor and destructor just with the specifications
`dest f (cons x y) = f x y`.
Since NLT kernel does not support simultaneous specification of multiple constants, we actually use
a combinator encoding to represent the tuple `(cons,dest)`.
---
obtain pair_tp where pair_tp_spec:
	if cons = pair_tp (const id), dest = pair_tp const
	then dest f (cons x y) = f x y;
	- for thesis if assm;
		apply assm[of ((dual ((∘) ∘ dual ∘ dual id) id |>) ∘ ((|>) |>))];
		- for cons if #simp for dest if #simp.
		.
	.

definition[as pair] (,) = pair_tp (const id).

definition pair_dest = pair_tp const.

lemma pair_dest#simp pair_dest f (x,y) = f x y;
	by pair_tp_spec[OF pair_def pair_dest_def].

definition pair_case = dual pair_dest.

lemma pair_case#simp pair_case (x,y) f = f x y;
	simp pair_case_def.

definition fst = pair_dest const.
definition snd = pair_dest (const id).

instance Pair; by #simp fst_def snd_def.

definition uncurry = dual ((∘) ∘ (∘)) (,).

lemma uncurry#simp uncurry f x y = f (x,y);
	simp uncurry_def.

definition pair_assoc = dual ((∘) ∘ (∘) ∘ (,)) (,).

lemma pair_assoc#simp pair_assoc x y z = (x,y,z);
	simp pair_assoc_def.

