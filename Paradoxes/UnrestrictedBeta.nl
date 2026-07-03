import Std, Eq.
fix (fun).
assume beta: (fun x. F.[x]) x = F.[x].

begin

interpret UnrestrictedAbbrev;
	- for F if assm: ∀f. (∀x. f x = F.[x]) ⟹ R then R;
		apply assm[of (fun x. F.[x])];
		- for x; unfold beta.
		.
	.

thm inconsistent. -- ∀false. false
