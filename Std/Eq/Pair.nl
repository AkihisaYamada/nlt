---
# Syntactic Pairing
---
fix (,) fst snd.
assume fst#simp fst (x,y) = x.
assume snd#simp snd (x,y) = y.

begin

instance pair: MetaInjective (,);
	- for x x' if eq: (,) x = (,) x' then x = x';
		have 1: fst (x,x) = fst (x',x);
			unfold eq.
		by 1[unfold fst].
	.

lemma pair_eq_pair_intro: if x: x = x', y: y = y' then (x,y) = (x',y');
	simp x y.

lemma pair_eq_pair_elim1: if eq: (x,y) = (x',y') then x = x';
	.. = fst (x,y).
	.. = fst (x',y'); unfold eq.
	.. = x'; unfold fst.
	.

lemma pair_eq_pair_elim2: if eq: (x,y) = (x',y') then y = y';
	.. = snd (x,y); unfold snd.
	.. = snd (x',y'); unfold eq.
	.. = y'; unfold snd.
	.

lemma pair_eq_pair_elim: if eq: (x,y) = (x',y'), assm: x = x' ⟹ y = y' ⟹ P then P;
	apply assm;
	by pair_eq_pair_elim1[OF eq] pair_eq_pair_elim2[OF eq].

lemma eq_pair_fst#simp[after 1] if p: p = (x,y) then fst p = x;
	simp p.

lemma eq_pair_snd#simp[after 1] if p: p = (x,y) then snd p = y;
	simp p.

---
One can obtain a pair `(Abs,Rep)`, such that `Rep (Abs x) = x`.
---
theory AbsRep begin

	obtain AbsRep where AbsRep_spec: snd AbsRep (fst AbsRep x) = x;
		- for thesis if assm;
			apply assm[of ((,) fst, snd)];
			- for x; simp.
			.
		.
	definition Abs = fst AbsRep.
	definition Rep = snd AbsRep.

	instance AbsRep: MetaInverse Abs Rep;
		by #simp Abs_def Rep_def AbsRep_spec.

	note#simp AbsRep.inverse.

end
