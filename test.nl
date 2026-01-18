print load.
import Class.
import ZF.

thy.

end


-----
## Classes
-----




define prop P := P ∨ ¬P.

lemma prop.intro1: P ⟹ prop P.
	assume P: P.
	by eq_prop2[OF prop.def or_intro1[OF P]].

lemma prop.intro2: P = false ⟹ prop P.
	assume nP: ¬P.
	by eq_prop2[OF prop.def or_intro2[OF nP]].

show prop.elim: prop P ⟹ (P ⟹ thesis) ⟹ (¬ P ⟹ thesis) ⟹ thesis.
	assume p: prop P.
	by or_elim[OF p[unfolded prop.def]](thesis).


show prop_imp: prop P ⟹ prop Q ⟹ prop (P ⟹ Q).
	assume p: prop P, q: prop Q.
	show 1: P ⟹ prop (P ⟹ Q).
		assume P: P.
		show 1.1: Q ⟹ prop (P ⟹ Q).
			assume Q: Q.
			show PQ: P ⟹ Q.
				by weaken[OF Q].
			by prop.intro1[OF PQ].
		show 1.2: ¬Q ⟹ prop (P ⟹ Q).
			assume nQ: ¬Q.
			show nPQ: ¬ (P ⟹ Q).
				by imp_not[OF P nQ].
			by prop.intro2[OF nPQ].
		by prop.elim[OF q 1.1 1.2].
	show 2: ¬P ⟹ prop (P ⟹ Q).
		assume nP: ¬P.
		show PQ: P ⟹ Q.
			by not_imp[OF nP].
		by prop.intro1[OF PQ].
	by prop.elim[OF p 1 2].

show prop_and: prop P ⟹ prop Q ⟹ prop (P ∧ Q).
	assume P: prop P, Q: prop Q.
	show 1: P ⟹ prop (P ∧ Q).
		assume P: P.
		show 1.1: Q ⟹ prop (P ∧ Q).
			assume Q: Q.
			by prop.intro1[OF and_intro[OF P Q]].
		show 1.2: ¬Q ⟹ prop (P ∧ Q).
			assume Q: ¬Q.
			by prop.intro2[OF not_and2[OF Q]](P).
		by prop.elim[OF Q 1.1 1.2].
	show 2: ¬P ⟹ prop (P ∧ Q).
		assume nP: ¬ P.
		by prop.intro2[OF not_and1[OF nP]](Q).
	by prop.elim[OF P 1 2].

show prop_or: prop P ⟹ prop Q ⟹ prop (P ∨ Q).
	assume p: prop P, q: prop Q.
	show 1: P ⟹ prop (P ∨ Q).
		assume P: P.
		by prop.intro1[OF or_intro1[OF P](Q)].
	show 2: ¬P ⟹ prop (P ∨ Q).
		assume nP: ¬P.
		show 3: Q ⟹ prop (P ∨ Q).
			assume Q: Q.
			by prop.intro1[OF or_intro2[OF Q]](P).
		show 4: ¬Q ⟹ prop (P ∨ Q).
			assume nQ: ¬Q.
			show nPnQ: ¬P ∧ ¬Q.
				by and_intro[OF nP nQ].
			show nor: ¬(P ∨ Q).
				by iff_elim2[OF Nor_iff nPnQ].
			by prop.intro2[OF nor].
		by prop.elim[OF q 3 4].
	by prop.elim[OF p 1 2].



define pred p := ∀x. prop (p x).

note pred.intro: eq_prop2[OF pred.def].
note pred.elim: eq_prop1[OF pred.def].







define reflexive A r := ∀a. a ∈ A ⟹ r a a.

note reflexive.intro: eq_prop2[OF reflexive.def].
note reflexive.elim: eq_prop1[OF reflexive.def].

show imp.reflexive: reflexive UNIV (⟹).
	show 1: ∀a. a ∈ UNIV ⟹ a ⟹ a.
		fix a.
		assume aU: a ∈ UNIV.
		by imp.refl(a).
	by reflexive.intro[OF 1].

define semi_attractive A r := ∀a. ∀b. ∀c. a ∈ A ⟹ b ∈ A ⟹ c ∈ A ⟹ r a b ⟹ r b a ⟹ r a c ⟹ r b c.

define transitive A r := ∀a. ∀b. ∀c. a ∈ A ⟹ b ∈ A ⟹ c ∈ A ⟹ r a b ⟹ r b c ⟹ r a c.

define antisymmetric A r := ∀a. ∀b. a ∈ A ⟹ b ∈ A ⟹ r a b ⟹ r b a ⟹ a = b.

define quasi_order A r := reflexive A r ∧ transitive A r.

define bound X r b := ∀x. x ∈ X ⟹ r x b.

define extreme X r e := e ∈ X ∧ bound X r e.

define dual r x y := r y x.

define extreme_bound A r X s := extreme (Collect (λ b. b ∈ A ∧ bound X r b)) (dual r) s.

define noetherian A r := ∀X. X ⊆ A ⟹ ∀x. x ≠ ∅ ⟹ ∃e. extreme X r e.

define well_related A r := noetherian A (dual r).

define well_order A r := well_related A r ∧ antisymmetric A r.

define well_complete A r := ∀X. X ⊆ A ⟹ well_order X r ⟹ ∃s. extreme_bound A r X s.

define monotone f A r r' := ∀a. a ∈ A ⟹ ∀b. b ∈ A ⟹ r a b ⟹ r' (f a) (f b).

show fixed_point:
	well_complete A r ⟹ semi_attractive A r ⟹
	monotone f A r r' ⟹ well_complete (Collect (λp. p ∈ A ∧ f p = p)) r.
	sorry.

define extremal X r x := x ∈ X ∧ (∀y. y ∈ X ⟹ ¬ r y x).

define well_founded A r := ∀X. X ⊆ A ⟹ X ≠ ∅ ⟹ ∃x. extremal X r x.



show NatGen.mono: monotone NatGen Set (⊆) (⊆).

assume eq_true: ∀ P. P ⟹ P = true.

assume eq_false: ∀ P. ¬ P ⟹ P = false.

define inJECTIVE f := (∀x. ∀x'. f x = f x' ⟹ x = x').


