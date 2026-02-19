import Eq.
fix (λ).
assume beta: (λx. F.[x]) x = F.[x].

begin

interpret CurryParadoxAbbrev;
	- for F if assm: ∀f. (∀x. f x = F.[x]) ⟹ R then R;
		apply assm[of (λx. F.[x])];
		- for x; unfold beta.
		.
	.

thm inconsistent.
