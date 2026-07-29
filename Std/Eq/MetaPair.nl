
--- Syntactic Pairing ---
fix (,) fst snd.
assume fst#simp fst (x,y) = x.
assume snd#simp snd (x,y) = y.

begin

interpret pair: MetaInjective (,);
	- for x x' if eq: (,) x = (,) x' then x = x';
		have 1: fst (x,x) = fst (x',x);
			unfold eq.
		by 1[unfold fst].
	.
lemma pair_eq_pair_intro: if x: x = x', y: y = y' then (x,y) = (x',y');
	simp x y.

lemma pair_eq_pair_elim1: if eq: (x,y) = (x',y') then x = x';
	have 1: x = fst (x,y).
	apply eq.trans[OF 1];
	have 2: fst (x,y) = fst (x',y');
		unfold eq.
	apply eq.trans[OF 2];
	have 3: fst (x',y') = x';
		unfold fst.
	by eq.trans[OF 3].

lemma pair_eq_pair_elim2: if eq: (x,y) = (x',y') then y = y';
	have 1: y = snd (x,y);
		unfold snd.
	apply eq.trans[OF 1];
	have 2: snd (x,y) = snd (x',y');
		unfold eq.
	apply eq.trans[OF 2];
	have 3: snd (x',y') = y';
		unfold snd.
	by eq.trans[OF 3].

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
obtain AbsRep where AbsRep_spec: snd AbsRep (fst AbsRep x) = x;
	- for thesis if assm;
		apply assm[of ((,) fst, snd)];
		- for x; simp.
		.
	.
define Abs = fst AbsRep.
define Rep = snd AbsRep.

interpret AbsRep: MetaInverse Abs Rep;
	by #simp Abs_def Rep_def AbsRep_spec.

note#simp AbsRep.inverse.
