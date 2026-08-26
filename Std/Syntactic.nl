fix id.
assume id_intro: if P.[x] then P.[id x].

fix const.
assume const_intro: if P.[c] then P.[const c x].

fix (∘).
assume o_intro: if P.[f (g x)] then P.[(f ∘ g) x].

fix dual.
assume dual_intro: if P.[f y x] then P.[dual f x y].

fix _BindAppBind.
assume _BindAppBind_intro: if P.[x. F.[x] G.[x]] then P.[ _BindAppBind (x. F.[x]) (x. G.[x])].

fix _BindConst.
assume _BindConst_intro: if P.[x. c] then P.[ _BindConst c].

begin

lemma id_elim: if assm: P.[id x] then P.[x];
	apply id_intro[of (z. P.[z] ⟹ P.[x]), OF imp.refl, OF assm].

lemma const_elim: if assm: P.[const c x] then P.[c];
	apply const_intro[of (z. P.[z] ⟹ P.[c]), OF imp.refl, OF assm].

lemma o_elim: if assm: P.[(f ∘ g) x] then P.[f (g x)];
	apply o_intro[of (z. P.[z] ⟹ P.[f (g x)]), OF imp.refl, OF assm].

lemma dual_elim: if assm: P.[dual f x y] then P.[f y x];
	apply dual_intro[of (z. P.[z] ⟹ P.[f y x]), OF imp.refl, OF assm].

lemma _BindAppBind_elim: if assm: P.[ _BindAppBind (x. F.[x]) (x. G.[x])] then P.[x. F.[x] G.[x]];
	apply _BindAppBind_intro[of (z. P.[z] ⟹ P.[x. F.[x] G.[x]]), OF imp.refl, OF assm].

lemma _BindConst_elim: if assm: P.[ _BindConst c] then P.[x. c];
	apply _BindConst_intro[of (z. P.[z] ⟹ P.[x. c]), OF imp.refl, OF assm].

