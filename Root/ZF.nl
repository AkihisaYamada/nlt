---
# Zermelo-Fraenkel Set Theory

We formalize intuitionistic ZF set theory in a conservative axiomatic form.
There, operations to derive sets from others are not explicit, but
only the existence of the resulting sets is axiomatized.
---
import Sets.
---
Standard formulations of ZF "define" pairs using unordered pairs,
but formalizing the unique choice axiom schema already requires syntactic pairing.
Moreover, to justify notation `upair (x,y)`, the pair argument must belong to a class.
(Notation `upair x y` would even require Currying.)
So we just assume syntactic pairs of sets are sets.
---
assume pair_set: ∀x ∈ Set. ∀y ∈ Set. (x,y) ∈ Set.
note! pair_set[rule].

begin