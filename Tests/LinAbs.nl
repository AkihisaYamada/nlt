---
# Linear Bracket Abstraction for Computing Combinator Expressions
---

import Std, Eq, Syntactic, MetaExt.
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

lemma: _RIP (⟨ 'a A P. ⟩ (∀x : 'a. x ∈ A ⟹ P.[x])) =
	dual ((∘) ∘ ((∘) ∘ (∀:))) ( _BinderApp _BindAppBind (y. (⟹) ∘ (y ∈))).

lemma: _RIP (⟨ i t e. ⟩ f t e i) = dual (dual ∘ f).
