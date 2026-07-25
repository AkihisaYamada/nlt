---
## Impredicatively Defined `⟺`

One can "define" `⟺` via equality, but the definition is impredicative and
does not justify why they should form propositions even if implication is
closed in propositions.
---
fix (⟺).
assume iff_eq_all: (P ⟺ Q) = (∀R. ((P ⟹ Q) ⟹ (Q ⟹ P) ⟹ R) ⟹ R).

begin

interpret base? TypeFree.Iff;
	- if PQ: P ⟹ Q, QP: Q ⟹ P then P ⟺ Q;
		unfold iff_eq_all;
		- for R if assm then R;
			by assm PQ QP.
		.
	- if PQ: P ⟺ Q;
		apply PQ[unfold iff_eq_all].
	- if PQ: P ⟺ Q;
		apply PQ[unfold iff_eq_all].
	.

interpret base.Eq;
	- for x y; apply iff_intro;
		- if xy: x = y; by #simp xy.
		- if assm; by assm[of (z. x = z), OF eq.refl].
		.
	.
