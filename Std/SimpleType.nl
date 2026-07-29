---
# Simple Type Theory

Church's simple type theory considers lambda terms and arrow types.
---
import Eq, Membership (:), Fun.
fix (→).
assume fun_to#intro if ∀x. x : A ⟹ F.[x] : B then (fun x. F.[x]) : A → B.
assume to_elim1#intro[after 1] if f : A → B, x : A then f x : B.

begin

lemma to_elim: if f: f : A → B, assm: (∀x. x : A ⟹ f x : B) ⟹ Q then Q;
	use f; by assm.

---
Type judgment of application can be reduced to that of the function,
if one knows the type of the argument.
---
lemma app_in#intro[after 1] if [x : A, f : A → B] then f x : B.

---
## Basic Combinators

### Identity
---
define id = fun x. x.

lemma id_type! id : A → A;
	unfold id_def.

lemma id_eq#simp[after 1] if x! x : A then id x = x;
	unfold id_def;
	apply fun_app_eq[OF _ x].


---
### Constant Function
---
define const = fun x y. x.

lemma const_type! const : A → B → A;
	unfold const_def.

lemma const_app#simp[after 1] if [x : A] then const x y = x;
	unfold const_def;
	unfold fun_app[of (A → A)];
	unfold fun_app[of A].

---
### Function Composition
---
define[as o] (∘) = fun f g x. f (g x).

lemma o_type: (∘) : (C → B) → (A → C) → A → B;
	unfold o_def.

lemma o_eq: if f! f : C → B, [g : A → C] then f ∘ g = fun x. f (g x);
	have 1: (∘) f = fun g x. f (g x);
		unfold o_def;
		apply fun_app[of ((A → C) → A → B)].
	unfold 1;
	apply fun_app[of (A → B)].

lemma o_app: if f! f : C → B, g! g : A → C, [x : A] then (f ∘ g) x = f (g x);
	unfold o_eq[OF f g];
	apply fun_app[of B].


---
### Pairs

One can encode a pair of `x` and `y` as a higher-order function `fun p. p x y`.
---
interpret Pair;
	obtain pair_tp where tp_spec:
		if (,) = pair_tp (fun x y z. x), fst = pair_tp (fun x y z. y), snd = pair_tp (fun x y z. z),
			(∀A B x y. x : A ⟹ y : B ⟹ fst (x,y) = x) ⟹
			(∀A B x y. x : A ⟹ y : B ⟹ snd (x,y) = y) ⟹ P
		then P;
		- for thesis if assm;

			define raw_pair = fun x y i. i x y.
			define raw_fst = fun p. p const.
			define raw_snd = fun p. p (fun x y. y).

			have raw_pair_type! raw_pair : A → B → (A → B → C) → C;
				unfold raw_pair_def.
			have raw_fst_type! raw_fst : ((A → B → A) → A) → A;
				unfold raw_fst_def.
			have raw_snd_type! raw_snd : ((A → B → B) → B) → B;
				unfold raw_snd_def.

			have raw_pair_app: if x! x : A then raw_pair x = fun y i. i x y;
				unfold raw_pair_def;
				apply fun_app[for B C, of (B → (A → B → C) → C)].

			have raw_pair_app2: if x! x : A, y! y : B then raw_pair x y = fun i. i x y;
				unfold raw_pair_app[OF x];
				apply fun_app[for C, of ((A → B → C) → C)].

			have raw_pair_app3: if x! x : A, y! y : B, i! i : A → B → C then raw_pair x y i = i x y;
				unfold raw_pair_app2[OF x y];
				unfold fun_app[of C].

			apply assm[of (fun p. p raw_pair raw_fst raw_snd)];
			- for (,) if pair0 for fst if fst0 for snd if snd0 for P if assm2;
				apply assm2;
				have pair: (,) = raw_pair;
					unfold pair0;
					apply in_fun_app_eq[OF raw_pair_type];
					have 1: (fun x y z. x) raw_pair = fun y z. raw_pair;
						apply in_fun_app_eq[for A B C D E, of (D → E → A → B → (A → B → C) → C)].
					unfold 1;
					have 2: (fun y z. raw_pair) raw_fst = fun z. raw_pair;
						apply in_fun_app_eq[for A B C E, of (E → A → B → (A → B → C) → C)].
					unfold 2;
					apply in_fun_app_eq[OF raw_pair_type].
				have fst: fst = raw_fst;
					unfold fst0;
					apply in_fun_app_eq[OF raw_fst_type];
					have 1: (fun x y z. y) raw_pair = fun y z. y;
						apply fun_app[for A B, of (A → B → A)].
					unfold 1;
					have 2: (fun y z. y) raw_fst = fun z. raw_fst;
						apply fun_app[for A B C, of (C → ((A → B → A) → A) → A)].
					unfold 2;
					apply fun_app[OF raw_fst_type].
				have snd: snd = raw_snd;
					unfold snd0;
					apply in_fun_app_eq[OF raw_snd_type];
					have 1: (fun x y z. z) raw_pair = fun y z. z;
						apply fun_app[for A B, of (A → B → A)].
					unfold 1;
					have 2: (fun y z. z) raw_fst = fun z. z;
						apply fun_app[for A, of (A → A)].
					unfold 2;
					apply in_fun_app_eq[OF raw_snd_type].
				- for A B x y if x!, y! then fst (x,y) = x;
					unfold pair fst raw_fst_def;
					apply fun_app_eq[of A];
					unfold raw_pair_app3[OF x y const_type].
				- for A B x y if x!, y! then snd (x,y) = y;
					unfold pair snd raw_snd_def;
					apply fun_app_eq[of B];
					have ty: (fun x y. y) : A → B → B.
					unfold raw_pair_app3[OF x y ty];
					unfold fun_app[of (B → B)];
					unfold fun_app[of B].
				.
			.
		.
	define[as pair] (,) = pair_tp (fun x y z. x).
	define fst = pair_tp (fun x y z. y).
	define snd = pair_tp (fun x y z. z).
	note spec: tp_spec[OF pair_def fst_def snd_def].
	- apply spec;
		- if fst, snd, x: x : A, y: y : B; by fst[OF x y].
		.
	- apply spec;
		- if fst, snd, x: x : A, y: y : B; by snd[OF x y].
		.
	.

thm fst_pair.
