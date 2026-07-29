import Eq, Membership.
fix (fun).
assume fun_app: for A F if F.[s] ∈ A then (fun x. F.[x]) s = F.[s].

begin

lemma fun_app_eq: for A if eq: F.[x] = t, ! t ∈ A then (fun x. F.[x]) s = t;
	... = F.[s];
		apply fun_app[of A];
		by #simp eq.
	... = t;
		by #simp eq.
	.

interpret Abbrev;
	- if assm: ∀f. (∀A x. F.[x] ∈ A ⟹ f x = F.[x]) ⟹ P then P;
		apply assm[of (fun x. F.[x])];
		by #elim fun_app.
	.

theory ArrowType :=
	fix (→).
	assume fun_to#intro if ∀x. x ∈ A ⟹ F.[x] ∈ B then (fun x. F.[x]) ∈ A → B.
	assume to_elim1: if f ∈ A → B, x ∈ A then f x ∈ B.
begin

	lemma to_elim: if f: f ∈ A → B, assm: (∀x. x ∈ A ⟹ f x ∈ B) ⟹ Q then Q;
		by assm to_elim1[OF f].

	---
	Type judgment of application can be reduced to that of the function,
	if one knows the type of the argument.
	---
	lemma app_in#intro[after 1] if x: x ∈ A, f: f ∈ A → B then f x ∈ B;
		by to_elim1[OF f x].

	define const = fun x y. x.

	lemma const_app_in_to! if [x ∈ A] then const x ∈ B → A;
		unfold const_def fun_app[of (B → A)].

	lemma const_app#simp[after 1] if [x ∈ A] then const x y = x;
		unfold const_def;
		unfold fun_app[of (A → A)];
		unfold fun_app[of A].

	define raw_pair = fun x y p. p x y.

	lemma raw_pair_in#intro[after 2] if [x ∈ A, y ∈ B] then raw_pair x y ∈ (A → B → C) → C;
		unfold raw_pair_def.

	lemma raw_pair_app: if [x ∈ A, y ∈ B, p ∈ A → B → C] then raw_pair x y p = p x y;
		unfold raw_pair_def;
		unfold fun_app[of (B → (A → B → C) → C)];
		unfold fun_app[of ((A → B → C) → C)];
		unfold fun_app[of C];
		.

	define raw_fst = fun p. p const.

	interpret raw_pair: Pair raw_pair raw_fst (fun x y. y);
		- if x! x ∈ A, y! y ∈ B then raw_fst (raw_pair x y) = x;
			unfold raw_fst_def;
			have 1: (fun p. p const) (raw_pair x y) = raw_pair x y const;
				apply fun_app[of A];

			thm const_app[OF raw_pair_in[OF x y, of id]].
foo
	interpret Pair;
		obtain tp where spec:
			if (,) = tp (fun x y z. x), fst = tp (fun x y z. y), snd = tp (fun x y z. z),
				(∀A B x y. x ∈ A ⟹ y ∈ B ⟹ fst (x,y) = x) ⟹
				(∀A B x y. x ∈ A ⟹ y ∈ B ⟹ snd (x,y) = y) ⟹ P
			then P;
			- for thesis if assm;
				apply assm[of (fun x y z p. p x y z)];
				- for (,) if c for fst if fst for snd if snd for P if assm2;
					apply assm2;
					- for A B x y if x!, y! then fst (x,y) = x;
						unfold fst;

end

theory FUNin :=
	fix FUN_∈ TYPE.
	assume TYPE: if A ∈ U then A ∈ TYPE U.
	assume fun_FUNin#intro if ∀x. x ∈ A ⟹ F.[x] ∈ B.[x] then (fun x. F.[x]) ∈ FUN x ∈ A. B.[x].
	assume FUNin_TYPE: if A ∈ TYPE U, ∀x. x ∈ A ⟹ B.[x] ∈ TYPE U then (FUN x ∈ A. B.[x]) ∈ TYPE U.
begin

	define[as to] (→) = fun A B. FUN x ∈ A. B.

end
