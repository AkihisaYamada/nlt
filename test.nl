------
# Untyped Lambda Calculus
------
base Root;

import Lambda;

setup conclude eq.refl;

setup rewrite eq.refl eq.sym eq.trans eq_prop1;

import Ext;

setup cong
	eq_cong: f x,
	eq_ext! x. α.[x];

setup define = λ beta;

----
## Defining Logical Constructs
----

define true := ∀P. P ⟹ P;

interpret True {
	substitute true;
		unfold true_def;
		by imp.refl;
}

setup conclude true_intro;

show true_eq_imp: if tP: true = P then P;
	fold tP;
	done;

show eq_true_imp: if Pt: P = true then P;
	unfold Pt;
	done;

define false := ∀P. P;

interpret False {
	substitute false;
		show! if f: false then P;
			by f[unfolded false_def];
		qed;
}

define (and_def) P ∧ Q := ∀ R. (P ⟹ Q ⟹ R) ⟹ R;

interpret And {
	for (∧);
	discharge if P: P, Q: Q then P ∧ Q;
		show 1: if PQR: P ⟹ Q ⟹ R then R;
			by PQR[OF P Q];
		by eq_prop2[OF and_def 1];
	discharge if PQ: P ∧ Q then P;
		show PQP: if P: P, Q: Q then P;
			by P;
		by eq_prop1[OF and_def][OF PQ PQP];
	discharge if PQ: P ∧ Q then Q;
		show PQQ: if P: P, Q: Q then Q;
			by Q;
		by eq_prop1[OF and_def][OF PQ PQQ];
}

define (iff_def) P ⟺ Q := (P ⟹ Q) ∧ (Q ⟹ P);

interpret Iff {
	for (⟺);
	discharge if PQ: P ⟹ Q, QP: Q ⟹ P then P ⟺ Q;
		show and: (P ⟹ Q) ∧ (Q ⟹ P);
			by and_intro[OF PQ QP];
		by and[folded iff_def];
	discharge if PQ: P ⟺ Q then P ⟹ Q;
		by and_elim1[OF PQ[unfolded iff_def]];
	discharge if PQ: P ⟺ Q then Q ⟹ P;
		by and_elim2[OF PQ[unfolded iff_def]];
}

show eq_imp_iff: if PQ: P = Q then P ⟺ Q;
	unfold PQ;
	by iff.refl;

show eq_commute: x = y ⟺ y = x;
	by iff_intro[OF eq.sym eq.sym];

define (not_def) ¬ P := P ⟹ false;

interpret Not {
	for false (¬);
	discharge if nP: ¬P, P: P then false;
		by nP[unfolded not_def][OF P];
	discharge if nP: P ⟹ false then ¬P;
		by nP[folded not_def];
}

define (or_def) P ∨ Q := ∀ R. (P ⟹ R) ⟹ (Q ⟹ R) ⟹ R;

interpret Or {
	for (∨);
	discharge if P: P then P ∨ Q;
		show 1: if PR: P ⟹ R, QR: Q ⟹ R then R;
			by PR[OF P];
		by eq_prop2[OF or_def 1];
	discharge if Q: Q then P ∨ Q;
		show 1: if PR: P ⟹ R, QR: Q ⟹ R then R;
			by QR[OF Q];
		by eq_prop2[OF or_def 1];
	discharge if PQ: P ∨ Q, PR: P ⟹ R, QR: Q ⟹ R then R;
		by eq_prop1[OF or_def PQ PR QR];
}

define (ex_def) ∃ α := (∀P. (∀x. α.[x] ⟹ P) ⟹ P);

interpret Ex {
	for (∃);
	discharge for x α, if ax: α.[x] then ∃x. α.[x];
		unfold ex_def;
		case for P, all: ∀x. α.[x] ⟹ P;
			by all[OF ax];
		qed;
	discharge if ex: ∃x. α.[x] then (∀x. α.[x] ⟹ P) ⟹ P;
		by ex[unfolded ex_def];
}

---
This is enough to interpret logic.
---
interpret UntypedLogic;

setup conclude iff.refl;

setup rewrite[iff] iff.refl iff.sym iff.trans iff_elim1;
setup cong[iff]
	iff_cong_imp: P ⟹ Q,
	iff_cong_iff: P ⟺ Q,
	iff_cong_and: P ∧ Q,
	iff_cong_or: P ∨ Q,
	iff_cong_not: ¬P,
	iff_cong_all! (∀x. α.[x]),
	iff_cong_ex! (∃x. α.[x]);

-----
## Assuming Unique Truth

At this point the logic is multi-valued, in the sense that true propositions are not necessarily equal.
We assume true propositions are all true.
-----
assume eq_true: P ⟹ P = true;

show eq_true_iff: P = true ⟺ P;
	by iff_intro[OF eq_true_imp eq_true];

show true_eq: if P: P then true = P;
	by eq.sym[OF eq_true[OF P]];

show true_eq_iff: true = P ⟺ P;
	by iff_intro[OF true_eq_imp true_eq];

show imp_true_eq: (P ⟹ true) = true;
	by eq_true[OF weaken[OF true_intro]];

show not_false_eq: (¬false) = true;
	apply eq_true;
	by not_false;

show true_and_true_eq: (true ∧ true) = true;
	by eq_true[OF true_and_true];

show true_or_eq: (true ∨ P) = true;
	by eq_true[OF true_or];

show or_true_eq: (P ∨ true) = true;
	by eq_true[OF or_true];

-- True is the left identity of implication.
assume true_imp_eq: (true ⟹ P) = P;

show not_true_eq: (¬true) = false;
	unfold not_def;
	by true_imp_eq;

show false_imp_eq: (false ⟹ P) = true;
	apply eq_true;
	by false_imp;

show and_false_eq: (P ∧ false) = false;
	unfold* and_def false_imp_eq imp_true_eq true_imp_eq;
	fold false_def;
	done;

show false_and_eq: (false ∧ P) = false;
	unfold* and_def false_imp_eq true_imp_eq;
	fold false_def;
	done;

show true_iff_false_eq: (true ⟺ false) = false;
	unfold* iff_def true_imp_eq false_and_eq;
	done;

show false_iff_true_eq: (false ⟺ true) = false;
	unfold* iff_def true_imp_eq and_false_eq;
	done;

show false_or_false_eq: (false ∨ false) = false;
oops

ctxt;

thm nex_nnot_iff;


-----
## More notions
-----

infix ≠ 50 50 50;

define (neq_def) x ≠ y := ¬ x = y;

show neq_intro: if xyf: x = y ⟹ false then x ≠ y;
	unfold neq_def;
	apply not_intro;
	by xyf;

note neq_elim: eq_prop1[OF neq_def];

show neq_irrefl: ¬ x ≠ x;
	unfold neq_def;
	apply nnot_intro;
	by eq.refl;

show true_Neq_false: true ≠ false;
	apply neq_intro;
	show! if tf: true = false then false;
		fold tf;
		by true_intro;
	qed;

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

show in_Prop: (P ∈ Prop) = (P = true ∨ P = false);
	unfold* Prop_def in_un in_Singleton;
	done;

note in_Prop_elim: if P: P ∈ Prop then or_elim[OF P[unfolded in_Prop]];

show true_in_Prop: true ∈ Prop;
	unfold in_Prop;
	unfold[iff]* iff_true[OF eq.refl] true_imp_iff iff_true[OF true_or] iff_true_iff;
	done;

show false_in_Prop: false ∈ Prop;
	unfold in_Prop;
	unfold[iff]* iff_true[OF eq.refl] iff_true[OF or_true] iff_true_iff;
	done;

show not_in_Prop: if p: P ∈ Prop then (¬P) ∈ Prop;
	apply in_Prop_elim[OF p];
	case P1: P = true;
		unfold* P1 not_true_eq;
		by false_in_Prop;
	case P0: P = false;
		unfold* P0 not_false_eq;
		by true_in_Prop;
	qed;

show imp_in_Prop: if P: P ∈ Prop, Q: Q ∈ Prop then (P ⟹ Q) ∈ Prop;
	apply in_Prop_elim[OF P];
	case P1: P = true;
		unfold* P1 true_imp_eq;
		by Q;
	case P0: P = false;
		unfold* P0 false_imp_eq;
		by true_in_Prop;
	qed;

show Prop_and: if p: P ∈ Prop, q: Q ∈ Prop then (P ∧ Q) ∈ Prop;
	apply in_Prop_elim[OF p];
	case P1: P = true;
		apply in_Prop_elim[OF q];
		case Q1: Q = true;
			unfold* P1 Q1 true_and_true_eq;
			by true_in_Prop;
		case Q0: Q = false;
			unfold* Q0 and_false_eq;
			by false_in_Prop;
		qed;
	case P0: P = false;
		unfold* P0 false_and_eq;
		by false_in_Prop;
	qed;

show Prop_or: if p: P ∈ Prop, q: Q ∈ Prop then (P ∨ Q) ∈ Prop;
	apply in_Prop_elim[OF p];
	case P1: P = true;
		unfold+ P1 true_or_eq;
		by true_in_Prop;
	case P0: P = false;
		apply in_Prop_elim[OF q];
		case Q1: Q = true;
			unfold+ Q1 or_true_eq;
			by true_in_Prop;
		case Q0: Q = false;
			unfold+ P0 Q0 false_or_false_eq;

show false_iff_eq: if p: P ∈ Prop then (false ⟺ P) = (¬P);
	apply in_Prop_elim[OF p];
	case P1: P = true;
		unfold* P1 false_iff_true_eq not_true_eq;
		done;
	case P0: P = false;
		unfold* P0 eq_true[OF iff.refl] not_false_eq;
		done;
	qed;

show true_iff_eq: if p: P ∈ Prop then (true ⟺ P) = P;
	apply in_Prop_elim[OF p];
	case P1: P = true;
		unfold* P1;
		by eq_true[OF iff.refl];
	case P0: P = false;
		unfold* P0 true_iff_false_eq;
		done;
	qed;

show iff_in_Prop: if p: P ∈ Prop, q: Q ∈ Prop then (P ⟺ Q) ∈ Prop;
	apply in_Prop_elim[OF p];
	case P1: P = true;
		unfold* P1 true_iff_eq[OF q];
		by q;
	case P0: P = false;
		unfold* P0 false_iff_eq[OF q];
		by not_in_Prop[OF q];
	qed;

show Prop_eq_iff: if p: P ∈ Prop, q: Q ∈ Prop then P = Q ⟺ (P ⟺ Q);
	apply in_Prop_elim[OF p];
	case P: P = true;
		unfold* P;
		unfold[iff]* true_eq_iff true_iff_iff;
		done;
	case P0: P = false;
		apply iff_intro;
		case PQ: P = Q;
			by eq_imp_iff[OF PQ];
		case PQ: P ⟺ Q;
			apply in_Prop_elim[OF q];
			case Q1: Q = true;
				show Q: Q; unfold Q1; done;
				show P: P; by Q[folded[iff] PQ];
				show 0: false; by P[unfolded P0];
				by false_imp[OF 0];
			case Q0: Q = false;
				unfold* P0 Q0;
				done;
			qed;
		qed;
	qed;



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


