import Std_Prop.Minimal.

begin

lemma eq_imp_iff#cong? if #simp P = Q, [P : Prop, Q : Prop] then P ⟷ Q;
	simp[on (=)].

extend Quantifiable begin

	lemma all_cong_eq#cong
		if AB: A = B, PQ: ∀x. x : A ⟹ P.[x] ⟷ Q.[x],
			[A : QTYPE, ∀x. x : A ⟹ P.[x] : Prop, ∀x. x : A ⟹ Q.[x] : Prop]
		then (∀x : A. P.[x]) ⟷ (∀x : B. Q.[x]);
		fold[on (=)] AB;
		apply all_cong_weak[OF PQ].

	lemma ex_cong_eq#cong
		if AB: A = B, PQ: ∀x. x : A ⟹ P.[x] ⟷ Q.[x],
			[A : QTYPE, ∀x. x : A ⟹ P.[x] : Prop, ∀x. x : A ⟹ Q.[x] : Prop]
		then (∃x : A. P.[x]) ⟷ (∃x : B. Q.[x]);
		fold[on (=)] AB;
		apply ex_cong_weak[OF PQ].

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

