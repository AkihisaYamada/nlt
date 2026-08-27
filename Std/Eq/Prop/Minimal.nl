import Std_Prop.Minimal, Comp.

begin
---
The notation for `≠` is defined using syntactic composition as follows.
---
definition[as neq] (≠) = ((¬) ∘) ∘ (=).

lemma neq_eq: (x ≠ y) = (¬(x = y));
	by #simp neq_def.

lemma neq_intro: for 'a if assm: x = y ⟹ false, [x : 'a, y : 'a, 'a : EQTYPE] then x ≠ y;
	by not_intro assm #simp neq_eq.

lemma eq_imp_iff: if #simp P = Q, [P : Prop, Q : Prop] then P ⟷ Q;
	simp[on (=)].

lemma iff_app_cong#cong? if #simp f = f', #simp x = x', [f x : Prop, f' x' : Prop] then f x ⟷ f' x';
	simp[on (=)].

lemma eq_iff_trans#trans if PQ: P = Q, QR: Q ⟷ R then P ⟷ R;
	apply QR[fold PQ].

extend Quantifiable begin

	lemma all_cong_eq#cong
		if AB: A = B, PQ: ∀x. intro (x : A) ⟹ P.[x] ⟷ Q.[x],
			[A : QTYPE, ∀x. x : A ⟹ P.[x] : Prop, ∀x. x : A ⟹ Q.[x] : Prop]
		then (∀x : A. P.[x]) ⟷ (∀x : B. Q.[x]);
		fold[on (=)] AB;
		by all_cong_weak PQ.

	lemma ex_cong_eq#cong
		if AB: A = B, PQ: ∀x. intro (x : A) ⟹ P.[x] ⟷ Q.[x],
			[A : QTYPE, ∀x. x : A ⟹ P.[x] : Prop, ∀x. x : A ⟹ Q.[x] : Prop]
		then (∃x : A. P.[x]) ⟷ (∃x : B. Q.[x]);
		fold[on (=)] AB;
		by ex_cong_weak PQ.

end

extend FirstOrder begin

	instance Quantifiable IND.

end

extend SecondOrder begin

	instance Quantifiable.

end

extend HigherOrder begin

	instance Quantifiable.

end

extend Membership begin

	instance Eq.Membership.

	theory TotalOrder :=
		import Connex, Order.
	begin
		instance TotalPreorder.
	end

end

instance Membership (:).

