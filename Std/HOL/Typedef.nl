---
## Type Definition

The type definition machineries of HOL proof assistants a la Gordon[^Gordon1988] are
the key for Church's simple type theory to be expressive enough for daily mathematics.

[^Gordon1988]
	Michael JC Gordon. HOL: A proof generating system for higher-order logic.
	VLSI specification, verification and synthesis. 1988. 73-128.

Type definition allows to turn a (polymorphic) predicate `t : σ ⇒ Prop`,
where `σ` contains $n$ distinct type variables `α_1`, ..., `α_n`,
into a new parametric type, `(α_1,...,α_n)τ` in HOL notation, accompanied by
- `abs_τ : σ ⇒ [α_1,...,α_n] τ` and
- `rep_τ : (α_1,...,α_n)τ ⇒ σ`,
such that
- if `a : σ` and `t a` then `rep_τ (abs_τ a) = a`; and
- if `x : (α_1,...,α_n)τ` then `t (rep_τ x)` and `abs_τ (rep_τ x) = x`.

The main question in formalizing this in NLT is how to handle multiple type parameters `α_1`, ..., `α_n`.
As naive logic supports `σ.[α]` for one parameter, by admitting *syntactic* paring `,` one can formalize the multiple parameters by `σ.[α_1,...,α_n]`. As suggested by the HOL notation `(α_1,...,α_n)τ` (for which we will use `τ (α_1,...,α_n)`), kernels of HOL systems must have a similar machinery at least for types.
---
import type.Prod.

---
For typed terms, HOL family derive pairs (product types) by type definition. I think this is just moving the assumption of the presence of pairs of terms into the presence of pairs of types.

Type definition machinery assumes that all types are inhabited, and allows to turn a polymorphic predicate into a parametric type, if a polymorphic witness that satisfies the predicate is provided.
Because the witness is required to be polymorphic, it is usually necessary to pick elements from type parameters. For this purpose we admit only the signature of Church's ι operator, without assuming any logical property.
---

assume typedef: for ARG Rep pred witness if
	  ∀X. X : ARG ⟹ pred X : Rep.[X] ⇒ Prop,-- `pred` is a polymorphic predicate over representations
	  ∀X. X : ARG ⟹ pred X (witness X),-- `witness` is a polymorphic witness of `pred`
	  ∀Abs abs rep.-- The existence of the three notions are postulated, such that
		Abs : ARG ⇒ TYPE ⟹
		(∀X. X : ARG ⟹ abs X : Rep.[X] ⇒ Abs X) ⟹
		(∀X. X : ARG ⟹ rep X : Abs X ⇒ Rep.[X]) ⟹
		(∀X. X : ARG ⟹ ∀a. a : Abs X ⟹ pred X (rep X a)) ⟹
		(∀X. X : ARG ⟹ ∀a. a : Abs X ⟹ abs X (rep X a) = a) ⟹
		(∀X. X : ARG ⟹ ∀x. x : Rep.[X] ⟹ pred X x ⟹ rep X (abs X x) = x) ⟹ thesis
	then thesis.
---

By capturing type definition of HOL kernel as a plain assumption, *local* type definitions[^KuncarP2019] are automatically available.

[^KuncarP2019]
	Ondřej Kunčar, Andrei Popescu. From Types to Sets by Local Type Definition in Higher-Order Logic.
	Journal of Automated Reasoning 62.2 (2019): 237-260.
---

begin

theory TypeDefinition ARG Rep pred :=
	assume pred_type: if X : ARG then pred X : Rep.[X] ⇒ Prop.
	assume nonempty: if ∀witness. (∀X. X : ARG ⟹ pred X (witness X)) ⟹ thesis then thesis.
begin

	obtain tp where
		tp_is_tuple: if ∀Abs abs rep. tp = (Abs,abs,rep) ⟹ thesis then thesis,
		tp_spec: if tp = (Abs,abs,rep),
			Abs : ARG ⇒ TYPE ⟹
			(∀X. X : ARG ⟹ abs X : Rep.[X] ⇒ Abs X) ⟹
			(∀X. X : ARG ⟹ rep X : Abs X ⇒ Rep.[X]) ⟹
			(∀X. X : ARG ⟹ ∀a. a : Abs X ⟹ pred X (rep X a)) ⟹
			(∀X. X : ARG ⟹ ∀a. a : Abs X ⟹ abs X (rep X a) = a) ⟹
			(∀X. X : ARG ⟹ ∀x. x : Rep.[X] ⟹ pred X x ⟹ rep X (abs X x) = x) ⟹ thesis
		then thesis;
	- for thesis' if assm;
		apply nonempty;
		- if witness: ∀X. X : ARG ⟹ pred X (witness X);
			apply typedef[OF pred_type witness];
			- for Abs abs rep if Abs_type!, abs_type, rep_type, rep, abs_rep, rep_abs;
				apply assm[of (Abs,abs,rep)];
				- for thesis if assm';
					by assm'[OF eq.refl].
				- for Abs' abs' rep' if eq for thesis if assm';
					have#simp Abs' = Abs; use eq[dual].
					have#simp abs' = abs; use eq[dual].
					have#simp rep' = rep; use eq[dual].
					apply assm';
					- by Abs_type.
					- by #intro[after 1] abs_type.
					- by #intro[after 1] rep_type.
					- by #intro[after 1] rep.
					- by #intro[after 1] abs_rep.
					- by #intro[after 1] rep_abs.
					.
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
		- if 1, 2, 3, 4, 5, 6;
			by 2[OF X].
		.
	lemma abs_ : for X if X: X : ARG, x: x : Rep.[X] then abs x = abs_ X x;
		simp abs_def IMPLICIT[OF x X].
 
	lemma abs_type: for X if X: X : ARG, x! x : Rep.[X] then abs x : Abs X;
		simp abs_ [OF X x]; apply abs__type[OF X, THEN to_elim1].

	lemma rep__type: if X: X : ARG then rep_ X : Abs X ⇒ Rep.[X];
		apply tp_spec[OF tp_eq];
		- if 1, 2, 3, 4, 5, 6;
			by 3[OF X].
		.
	lemma rep_ : for X if X: X : ARG, a! a : Abs X then rep a = rep_ X a;
		simp rep_def IMPLICIT[of X (X. Abs X), OF a X].

	lemma rep_type: for X if X! X : ARG, a! a : Abs X then rep a : Rep.[X];
		simp rep_ [OF X a]; apply rep__type[THEN to_elim1].

	lemma rep: for X if X: X : ARG, a: a : Abs X then pred X (rep a);
		apply tp_spec[OF tp_eq];
		- if 1, 2, 3, 4, 5, 6;
			simp rep_ [OF X a]; by 4[OF X a].
		.

	lemma abs_rep: for X if X: X : ARG, a: a : Abs X then abs (rep a) = a;
		apply tp_spec[OF tp_eq];
		- if 1, 2, 3, 4, 5, 6;
			unfold abs_ [OF X rep_type[OF X a]], rep_ [OF X a]; by 5[OF X a].
		.

	lemma rep_abs: for X if X: X : ARG, px: pred X x, x: x : Rep.[X] then rep (abs x) = x;
		apply tp_spec[OF tp_eq];
		- if 1, 2, 3, 4, 5, 6;
			unfold rep_ [OF X abs_type[OF X x]], abs_ [OF X x]; by 6[OF X x px].
		.
	lemma rep_eq_imp_abs_eq: for X if X! X : ARG, rep: rep a = x, [a : Abs X] then abs x = a;
		fold rep; apply abs_rep[OF X].

end
