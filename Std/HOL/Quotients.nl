---
# Quotients

HOL family defines sets as predicates via the `typedef` mechanism. So defined types behave as sets, because Gordon's HOL admits both
- functional extensionality: `f = g` if they are of type `'a -> 'b` and `∀x. x : 'a ⟹ f x = g x`; and
- propositional extensionality: `P = Q` if they are propositions and `P ⟷ Q`.
Church's original formulation mentions the former as an axiom necessary "in order to obtain classical real number theory", and does not mention the latter.

If we admit quotient types instead of `typedef`, we can define sets as (intentional) predicates quotiented by extensional equivalence. I believe this is closer to usual mathematicians mind, who would not think `1 = 1` and `∀x y z n ∈ ℕ. x^n + y^n = z^n ⟹ n ≤ 2` are identical.
Moreover,
- quotient does not require witness inhabitant, which is automatic when the representation type is inhabited
- when all types are inhabited, `typedef` is derivable.
---
import Relations, type.Prod.

assume quotient_type: for ARG Rep eq if
	  ∀X. X : ARG ⟹ Rep.[X] : TYPE,
	  ∀X. X : ARG ⟹ eq X : Rep.[X] ⇒ Rep.[X] ⇒ Prop,-- `eq` is a polymorphic relation over representations
	  ∀X. X : ARG ⟹ equivalence Rep.[X] (eq X),-- `eq` is an equivalence
	  ∀Abs abs rep.-- The existence of the three notions are postulated, such that
		Abs : ARG ⇒ TYPE ⟹
		(∀X. X : ARG ⟹ abs X : Rep.[X] ⇒ Abs X) ⟹
		(∀X. X : ARG ⟹ rep X : Abs X ⇒ Rep.[X]) ⟹
		(∀X. X : ARG ⟹ ∀x. x : Rep.[X] ⟹ ∀a. a : Abs X ⟹ abs X x = a ⟹ eq X x (rep X a)) ⟹
		(∀X. X : ARG ⟹ ∀x. x : Rep.[X] ⟹ ∀a. a : Abs X ⟹ eq X x (rep X a) ⟹ abs X x = a) ⟹ thesis
	then thesis.

begin

theory QuotientType ARG Rep eq :=
	assume Rep_type! if X : ARG then Rep.[X] : TYPE.
	assume eq_type! if X : ARG then eq X : Rep.[X] ⇒ Rep.[X] ⇒ Prop.
	assume equivalence: if X : ARG then equivalence Rep.[X] (eq X).
begin

	obtain tp where
		tp_is_tuple: if ∀Abs abs rep. tp = (Abs,abs,rep) ⟹ thesis then thesis,
		tp_spec: if tp = (Abs,abs,rep),
			Abs : ARG ⇒ TYPE ⟹
			(∀X. X : ARG ⟹ abs X : Rep.[X] ⇒ Abs X) ⟹
			(∀X. X : ARG ⟹ rep X : Abs X ⇒ Rep.[X]) ⟹
			(∀X. X : ARG ⟹ ∀x. x : Rep.[X] ⟹ ∀a. a : Abs X ⟹ abs X x = a ⟹ eq X x (rep X a)) ⟹
			(∀X. X : ARG ⟹ ∀x. x : Rep.[X] ⟹ ∀a. a : Abs X ⟹ eq X x (rep X a) ⟹ abs X x = a) ⟹ thesis
		then thesis;
	- for thesis if assm;
		apply quotient_type[OF Rep_type eq_type equivalence];
		- for Abs abs rep if 1, 2, 3, 4, 5;
			apply assm[of (Abs,abs,rep)];
			- for thesis' if assm'; apply assm'[OF eq.refl].
			- for Abs' abs' rep' if eq for thesis' if assm';
				have#simp Abs' = Abs; apply eq.sym; use eq.
				have#simp abs' = abs; apply eq.sym; use eq.
				have#simp rep' = rep; apply eq.sym; use eq.
				apply assm';
				- by 1.
				- for X; by #intro[after 1] 2.
				- for X; by #intro[after 1] 3.
				- for X; by #intro[after 1] 4.
				- for X; by #intro[after 1] 5.
				.
			.
		.
	.

	definition Abs = fst tp.
	definition abs_ = fst (snd tp).
	definition rep_ = snd (snd tp).

	definition abs = (IMPLICIT X : ARG. Rep.[X]) abs_.
	definition rep = (IMPLICIT X : ARG. Abs X) rep_.

	lemma tp_eq: tp = (Abs, abs_ , rep_ );
		apply tp_is_tuple;
		- if eq: tp = (Abs',abs',rep');
			unfold! eq Abs_def abs__def rep__def.
		.

	lemma Abs_type: Abs : ARG ⇒ TYPE;
		apply tp_spec[OF tp_eq].
	note Abs_type1: Abs_type[THEN to_elim1].

	lemma abs__type: if X: X : ARG then abs_ X : Rep.[X] ⇒ Abs X;
		apply tp_spec[OF tp_eq];
		- if 1, 2, 3, 4, 5;
			by 2[OF X].
		.
	lemma abs_ : for X if X: X : ARG, x: x : Rep.[X] then abs x = abs_ X x;
		simp abs_def IMPLICIT[OF x X].
 
	lemma abs_type! for X if X: X : ARG, x! x : Rep.[X] then abs x : Abs X;
		simp abs_ [OF X x]; apply abs__type[OF X, THEN to_elim1].

	lemma rep__type: if X: X : ARG then rep_ X : Abs X ⇒ Rep.[X];
		apply tp_spec[OF tp_eq];
		- if 1, 2, 3, 4, 5;
			by 3[OF X].
		.
	lemma rep_ : for X if X: X : ARG, a! a : Abs X then rep a = rep_ X a;
		simp rep_def IMPLICIT[of X (X. Abs X), OF a X].

	lemma rep_type! for X if X! X : ARG, a! a : Abs X then rep a : Rep.[X];
		simp rep_ [OF X a]; apply rep__type[THEN to_elim1].

	lemma abs_rep: for X
		if abs: abs x = a, X: X : ARG, x: x : Rep.[X], a: a : Abs X then eq X x (rep a);
		apply tp_spec[OF tp_eq];
		- if 1, 2, 3, 4, 5; unfold rep_ [OF X a]; apply 4[OF X x a]; fold abs_ [OF X x]; apply abs.
		.

	lemma rep_abs: for X
		if rep: eq X x (rep a), X: X : ARG, x: x : Rep.[X], a: a : Abs X then abs x = a;
		apply tp_spec[OF tp_eq];
		- if 1, 2, 3, 4, 5; unfold abs_ [OF X x]; apply 5[OF X x a]; fold rep_ [OF X a]; apply rep.
		.

	lemma abs_rep_eq: for X
		if [X : ARG, a : Abs X] then abs (rep a) = a;
	-	interpret equivalence (Rep.[X]) (eq X);
			show: equivalence (Rep.[X]) (eq X); apply equivalence[of X].
			.
		apply rep_abs[of X];
		by refl.
	.

	lemma rep_abs_sim: for X
		if [X : ARG, x : Rep.[X]] then eq X (rep (abs x)) x;
	-	interpret equivalence (Rep.[X]) (eq X);
			show: equivalence (Rep.[X]) (eq X); apply equivalence[of X].
			.
		apply sym, abs_rep.
	.

	lemma eq_intro: for X
		if eq: eq X (rep a) (rep b), [X : ARG, a : Abs X, b : Abs X] then a = b;
		.. = abs (rep a); apply eq.sym, abs_rep_eq[of X].
		apply rep_abs[of X], eq.

end

extend Inhabited begin

	definition typedef_prj =
		(fun 'a : TYPE, pred : 'a → Prop, x : 'a. if pred x then x else such z : 'a. false).
	instance Typedef;
		- for ARG Rep pred witness
			if pred_type, witness for thesis if assm then thesis;
			interpret QuotientType ARG Rep (fun 'X : ARG, x y : Rep.['X].
				(  = y ∨  

end
