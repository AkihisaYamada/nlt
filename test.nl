base Lambda;



-----
## More notions
-----

prefix ∃! 0 0;

define (ex1_def) (∃!) α := ∃x. α.[x] ∧ (∀y. α.[y] ⟹ x = y);

show ex1_intro: for x, if x: α.[x], 1: (∀y. α.[y] ⟹ x = y) then (∃!) α;
	unfold ex1_def;
	apply ex_intro1(x);
	show! α.[x] ∧ (∀y. α.[y] ⟹ x = y);
		apply and_intro;
		note! x;
		by 1;
	qed;

show ex1_elim: if ex1: (∃!) α, body: ∀x. α.[x] ⟹ (∀y. α.[y] ⟹ x = y) ⟹ P then P;
	obtain x where and: (α.[x]) ∧ (∀y. α.[y] ⟹ x = y);
		by ex1[unfolded+ ex1_def ex_def];
	show ax: α.[x];
		by and_elim1[OF and];
	show 1: ∀y. α.[y] ⟹ x = y;
		by and_elim2[OF and];
	by body[OF ax 1];


-----
## More Axioms for Constructors
-----

prefix THE 0 1;
fix THE;
assume ex1_imp_THE: (∃!) α ⟹ α.[(THE) α];

show ex1_imp_THE_eq: if ex1: (∃!) α, x: α.[x] then (THE) α = x;
	apply ex1_elim[OF ex1];
	show! if az: α.[z], 1: ∀y. α.[y] ⟹ z = y then (THE) α = x;
		show zx: z = x;
			by 1[OF x];
		show zT: z = (THE) α;
			by 1[OF ex1_imp_THE[OF ex1]];
		by zx[unfolded zT];
	qed;

fix Const is_const;

assume Const_is_const: is_const Const;

assume Const_neq_app: is_const c ⟹ Const ≠ c x;

assume const_app: is_const c ⟹ is_const (c x);

assume const_app_eq_app: is_const c ⟹ is_const d ⟹ c x = d y ⟹ c = d ∧ x = y;

define const_arg v := (THE x. ∃ c. is_const c ∧ v = c x);

thm const_arg_def;

show const_arg: if c: is_const c then const_arg (c x) = x;
	unfold const_arg_def;
	apply ex1_imp_THE_eq;
	apply ex1_intro(x);
	apply ex_intro1(c);
	apply and_intro;
	note! c;
	note! eq.refl;
	show! if ex: ∃c'. is_const c' ∧ c x = c' y then x = y;
		obtain c' where c': is_const c', cc': c x = c' y;
			note 1: ex[unfolded ex_def];
			note 2: 1[unfolded[iff] and_imp_iff];
			by 2;
		note and: const_app_eq_app[OF c c' cc'];
		by and_elim2[OF and];
	show! ∃c'. is_const c' ∧ c x = c' x;
		apply ex_intro1(c);
		apply and_intro;
		note! c;
		note! eq.refl;
		qed;
	qed;

fix IF;
assume IF_true: IF true x y = x;
assume IF_false: IF false x y = y;

-----
## Classes
-----

define Collect := Const true;

show Collect_is_const: is_const Collect;
	unfold Collect_def;
	apply const_app;
	by Const_is_const;

show const_arg_Collect: const_arg (Collect P) = P;
	by const_arg[OF Collect_is_const];

infix ∈ 50 50 50;

obtain ∈ where in_Collect: ∀x. ∀P. (x ∈ Collect P) = P x;
	case for thesis, 1: ∀in. (∀x. ∀P. in x (Collect P) = P x) ⟹ thesis;
		define (in_def) x ∈ X := const_arg X x;
		show 2: (x ∈ Collect P) = P x;
			unfold in_def;
			unfold const_arg_Collect;
			by eq.refl;
		by 1[OF 2];
	qed;

infix ∋ 50 50 50;
define (has_eq_in) X ∋ x := x ∈ X;



define ∅ := Collect (λx. false);

define Singleton x := Collect (λy. y = x);

infix ∪ 61 60 61;
define (un_def) X ∪ Y := Collect (λx. x ∈ X ∨ x ∈ Y);

setup set_comprehension ∅ Singleton Collect (λ) (∪);

show in_un: (x ∈ X ∪ Y) = (x ∈ X ∨ x ∈ Y);
	unfold* un_def in_Collect beta;
	done;

define UNIV := {x. true};

show in_Singleton: (x ∈ {y}) = (x = y);
	unfold* Singleton_def in_Collect beta;
	done;

----
### The Set of Propositions
----

define Prop := {true, false};


infix ` 100 100 100;

define (image_def) f ` X := {y. ∃x. x ∈ X ∧ y = f x};

show in_image: (y ∈ f ` X) = (∃x. x ∈ X ∧ y = f x);
	unfold+ image_def in_Collect beta;
	done;

infix ⊆ 50 50 50;

define (subset_def) X ⊆ Y := ∀x. x ∈ X ⟹ x ∈ Y;

infix → 61 60 60;
define (map_def) X → Y := {f. f ` X ⊆ Y};

define Class := Collect ` (UNIV → Prop);

show in_Class: (X ∈ Class) = (∃p. p ∈ UNIV → Prop ∧ X = Collect p);

oops


define (MEET) ⋂ XX := {x. ∀X. X ∈ XX ⟹ x ∈ X};

show MEET_in_Class: XX ⊆ Class ⟹ ⋂ XX ∈ Class;
	assume XX: XX ⊆ Class;
	show 1: ⋂ XX = {x. ∀X. X ∈ XX ⟹ x ∈ X};
		by MEET.def;
	show prop: ∀x. (∀X. X ∈ XX ⟹ x ∈ X) ∈ Prop;
		fix x;
		
	show prop: ∀x. prop ((λx. ∀X. X ∈ XX ⟹ x ∈ X) x);
	show pred: pred (λx. ∀X. X ∈ XX ⟹ x ∈ X);
		by pred.intro[OF prop];
	show 1: ∃p. pred p ∧ ⋂ XX = Collect p;
		sorry;
	sorry;

infix ∉ 50 50 50;
define x ∉ X := ¬ x ∈ X;

define Russel := {X. X ∉ X};

define 0 := Const false;
define Suc := Const 0;

define Nat := ⋂ {X. 0 ∈ X ∧ Suc ` X ⊆ X};





define prop P := P ∨ ¬P;

show prop.intro1: P ⟹ prop P;
	assume P: P;
	by eq_prop2[OF prop.def or_intro1[OF P]];

show prop.intro2: P = false ⟹ prop P;
	assume nP: ¬P;
	by eq_prop2[OF prop.def or_intro2[OF nP]];

show prop.elim: prop P ⟹ (P ⟹ thesis) ⟹ (¬ P ⟹ thesis) ⟹ thesis;
	assume p: prop P;
	by or_elim[OF p[unfolded prop.def]](thesis);


show prop_imp: prop P ⟹ prop Q ⟹ prop (P ⟹ Q);
	assume p: prop P, q: prop Q;
	show 1: P ⟹ prop (P ⟹ Q);
		assume P: P;
		show 1.1: Q ⟹ prop (P ⟹ Q);
			assume Q: Q;
			show PQ: P ⟹ Q;
				by weaken[OF Q];
			by prop.intro1[OF PQ];
		show 1.2: ¬Q ⟹ prop (P ⟹ Q);
			assume nQ: ¬Q;
			show nPQ: ¬ (P ⟹ Q);
				by imp_not[OF P nQ];
			by prop.intro2[OF nPQ];
		by prop.elim[OF q 1.1 1.2];
	show 2: ¬P ⟹ prop (P ⟹ Q);
		assume nP: ¬P;
		show PQ: P ⟹ Q;
			by not_imp[OF nP];
		by prop.intro1[OF PQ];
	by prop.elim[OF p 1 2];

show prop_and: prop P ⟹ prop Q ⟹ prop (P ∧ Q);
	assume P: prop P, Q: prop Q;
	show 1: P ⟹ prop (P ∧ Q);
		assume P: P;
		show 1.1: Q ⟹ prop (P ∧ Q);
			assume Q: Q;
			by prop.intro1[OF and_intro[OF P Q]];
		show 1.2: ¬Q ⟹ prop (P ∧ Q);
			assume Q: ¬Q;
			by prop.intro2[OF not_and2[OF Q]](P);
		by prop.elim[OF Q 1.1 1.2];
	show 2: ¬P ⟹ prop (P ∧ Q);
		assume nP: ¬ P;
		by prop.intro2[OF not_and1[OF nP]](Q);
	by prop.elim[OF P 1 2];

show prop_or: prop P ⟹ prop Q ⟹ prop (P ∨ Q);
	assume p: prop P, q: prop Q;
	show 1: P ⟹ prop (P ∨ Q);
		assume P: P;
		by prop.intro1[OF or_intro1[OF P](Q)];
	show 2: ¬P ⟹ prop (P ∨ Q);
		assume nP: ¬P;
		show 3: Q ⟹ prop (P ∨ Q);
			assume Q: Q;
			by prop.intro1[OF or_intro2[OF Q]](P);
		show 4: ¬Q ⟹ prop (P ∨ Q);
			assume nQ: ¬Q;
			show nPnQ: ¬P ∧ ¬Q;
				by and_intro[OF nP nQ];
			show nor: ¬(P ∨ Q);
				by iff_elim2[OF Nor_iff nPnQ];
			by prop.intro2[OF nor];
		by prop.elim[OF q 3 4];
	by prop.elim[OF p 1 2];



define pred p := ∀x. prop (p x);

note pred.intro: eq_prop2[OF pred.def];
note pred.elim: eq_prop1[OF pred.def];







define reflexive A r := ∀a. a ∈ A ⟹ r a a;

note reflexive.intro: eq_prop2[OF reflexive.def];
note reflexive.elim: eq_prop1[OF reflexive.def];

show imp.reflexive: reflexive UNIV (⟹);
	show 1: ∀a. a ∈ UNIV ⟹ a ⟹ a;
		fix a;
		assume aU: a ∈ UNIV;
		by imp.refl(a);
	by reflexive.intro[OF 1];

define semi_attractive A r := ∀a. ∀b. ∀c. a ∈ A ⟹ b ∈ A ⟹ c ∈ A ⟹ r a b ⟹ r b a ⟹ r a c ⟹ r b c;

define transitive A r := ∀a. ∀b. ∀c. a ∈ A ⟹ b ∈ A ⟹ c ∈ A ⟹ r a b ⟹ r b c ⟹ r a c;

define antisymmetric A r := ∀a. ∀b. a ∈ A ⟹ b ∈ A ⟹ r a b ⟹ r b a ⟹ a = b;

define quasi_order A r := reflexive A r ∧ transitive A r;

define bound X r b := ∀x. x ∈ X ⟹ r x b;

define extreme X r e := e ∈ X ∧ bound X r e;

define dual r x y := r y x;

define extreme_bound A r X s := extreme (Collect (λ b. b ∈ A ∧ bound X r b)) (dual r) s;

define noetherian A r := ∀X. X ⊆ A ⟹ ∀x. x ≠ ∅ ⟹ ∃e. extreme X r e;

define well_related A r := noetherian A (dual r);

define well_order A r := well_related A r ∧ antisymmetric A r;

define well_complete A r := ∀X. X ⊆ A ⟹ well_order X r ⟹ ∃s. extreme_bound A r X s;

define monotone f A r r' := ∀a. a ∈ A ⟹ ∀b. b ∈ A ⟹ r a b ⟹ r' (f a) (f b);

show fixed_point:
	well_complete A r ⟹ semi_attractive A r ⟹
	monotone f A r r' ⟹ well_complete (Collect (λp. p ∈ A ∧ f p = p)) r;
	sorry;

define extremal X r x := x ∈ X ∧ (∀y. y ∈ X ⟹ ¬ r y x);

define well_founded A r := ∀X. X ⊆ A ⟹ X ≠ ∅ ⟹ ∃x. extremal X r x;



show NatGen.mono: monotone NatGen Set (⊆) (⊆);

assume eq_true: ∀ P. P ⟹ P = true;

assume eq_false: ∀ P. ¬ P ⟹ P = false;

define inJECTIVE f := (∀x. ∀x'. f x = f x' ⟹ x = x');


