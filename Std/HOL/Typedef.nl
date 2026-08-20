---
## Type Definition

The type definition machineries of HOL proof assistants a la Gordon[^Gordon1988] are
the key for Church's simple type theory to be expressive enough for daily mathematics.

[^Gordon1988]
	Michael JC Gordon. HOL: A proof generating system for higher-order logic.
	VLSI specification, verification and synthesis. 1988. 73-128.

Type definition allows to turn a (polymorphic) predicate `t : σ → Prop`,
where `σ` contains $n$ distinct type variables `α_1`, ..., `α_n`,
into a new parametric type, `(α_1,...,α_n)τ` in HOL notation, accompanied by
- `Abs_τ : σ → [α_1,...,α_n] τ` and
- `Rep_τ : (α_1,...,α_n)τ → σ`,
such that
- if `a : σ` and `t a` then `Rep_τ (Abs_τ a) = a`; and
- if `x : (α_1,...,α_n)τ` then `t (Rep_τ x)` and `Abs_τ (Rep_τ x) = x`.

The main question in formalizing this in NLT is how to handle multiple type parameters `α_1`, ..., `α_n`.
As naive logic supports `σ.[α]` for one parameter, by admitting *syntactic* paring `,` one can formalize the multiple parameters by `σ.[α_1,...,α_n]`. As suggested by the HOL notation `(α_1,...,α_n)τ` (for which we will use `τ (α_1,...,α_n)`), kernels of HOL systems must have a similar machinery at least for types.
---
import type.Prod.

---
For typed terms, HOL family derive pairs (product types) by type definition. I think this is just moving the assumption of the presence of pairs of terms into the presence of pairs of types.

Type definition machinery assumes that all types are inhabited, and allows to turn a polymorphic predicate into a parametric type, if a polymorphic witness that satisfies the predicate is provided.
Because the witness is required to be polymorphic, it is usually necessary to pick elements from type parameters. For this purpose we admit only the signature of Church's ι operator, without assuming any logical property.
---

assume typedef: for ARG REP pred witness if
	  ∀X. X : ARG ⟹ pred X : REP.[X] → Prop,-- `pred` is a polymorphic predicate over representations
	  ∀X. X : ARG ⟹ pred X (witness X),-- `witness` is a polymorphic witness of `pred`
	  ∀ABS Abs Rep.-- The existence of the three notions are postulated, such that
		ABS : ARG → TYPE ⟹
		(∀X. X : ARG ⟹ Abs X : REP.[X] → ABS X) ⟹
		(∀X. X : ARG ⟹ Rep X : ABS X → REP.[X]) ⟹
		(∀X. X : ARG ⟹ ∀a. a : ABS X ⟹ pred X (Rep X a)) ⟹
		(∀X. X : ARG ⟹ ∀a. a : ABS X ⟹ Abs X (Rep X a) = a) ⟹
		(∀X. X : ARG ⟹ ∀x. x : REP.[X] ⟹ pred X x ⟹ Rep X (Abs X x) = x) ⟹ thesis
	then thesis.
---

By capturing type definition of HOL kernel as a plain assumption, *local* type definitions[^KuncarP2019] are automatically available.

[^KuncarP2019]
	Ondřej Kunčar, Andrei Popescu. From Types to Sets by Local Type Definition in Higher-Order Logic.
	Journal of Automated Reasoning 62.2 (2019): 237-260.

---

begin

theory TypeDefinition ARG REP pred :=
	assume pred_type: if X : ARG then pred X : REP.[X] → Prop.
	assume nonempty: if ∀witness. (∀X. X : ARG ⟹ pred X (witness X)) ⟹ thesis then thesis.
begin

	obtain tp where
		tp_is_tuple: if ∀ABS Abs Rep. tp = (ABS,Abs,Rep) ⟹ thesis then thesis,
		tp_spec: if tp = (ABS,Abs,Rep),
			ABS : ARG → TYPE ⟹
			(∀X. X : ARG ⟹ Abs X : REP.[X] → ABS X) ⟹
			(∀X. X : ARG ⟹ Rep X : ABS X → REP.[X]) ⟹
			(∀X. X : ARG ⟹ ∀a. a : ABS X ⟹ pred X (Rep X a)) ⟹
			(∀X. X : ARG ⟹ ∀a. a : ABS X ⟹ Abs X (Rep X a) = a) ⟹
			(∀X. X : ARG ⟹ ∀x. x : REP.[X] ⟹ pred X x ⟹ Rep X (Abs X x) = x) ⟹ thesis
		then thesis;
	- for thesis' if assm;
		apply nonempty;
		- if witness: ∀X. X : ARG ⟹ pred X (witness X);
			apply typedef[OF pred_type witness];
			- for ABS Abs Rep if ABS_type!, Abs_type, Rep_type, Rep, Abs_Rep, Rep_Abs;
				apply assm[of (ABS,Abs,Rep)];
				- for thesis if assm';
					by assm'[OF eq.refl].
				- for ABS' Abs' Rep' if eq for thesis if assm';
					have#simp ABS' = ABS; use eq[dual].
					have#simp Abs' = Abs; use eq[dual].
					have#simp Rep' = Rep; use eq[dual].
					apply assm';
					- by ABS_type.
					- by #intro[after 1] Abs_type.
					- by #intro[after 1] Rep_type.
					- by #intro[after 1] Rep.
					- by #intro[after 1] Abs_Rep.
					- by #intro[after 1] Rep_Abs.
					.
				.
			.
		.
	.

	definition ABS = fst tp.
	definition Abs = fst (snd tp).
	definition Rep = snd (snd tp).

	lemma tp_eq: tp = (ABS,Abs,Rep);
		apply tp_is_tuple;
		- if eq: tp = (ABS',Abs',Rep');
			unfold! eq ABS_def Abs_def Rep_def.
		.

	lemma ABS_type: ABS : ARG → TYPE;
		apply tp_spec[OF tp_eq].
	note ABS_type1: ABS_type[THEN to_elim1].

	lemma Abs_type: if X: X : ARG then Abs X : REP.[X] → ABS X;
		apply tp_spec[OF tp_eq];
		- if 1, 2, 3, 4, 5, 6;
			by 2[OF X].
		.
	note Abs_type1: Abs_type[THEN to_elim1].

	lemma Rep_type: if X: X : ARG then Rep X : ABS X → REP.[X];
		apply tp_spec[OF tp_eq];
		- if 1, 2, 3, 4, 5, 6;
			by 3[OF X].
		.
	note Rep_type1: Rep_type[THEN to_elim1].

	lemma Rep: if a: a : ABS X, X: X : ARG then pred X (Rep X a);
		apply tp_spec[OF tp_eq];
		- if 1, 2, 3, 4, 5, 6;
			by 4[OF X a].
		.

	lemma Abs_Rep: if X: X : ARG, a: a : ABS X then Abs X (Rep X a) = a;
		apply tp_spec[OF tp_eq];
		- if 1, 2, 3, 4, 5, 6;
			by 5[OF X a].
		.

	lemma Rep_Abs: if X: X : ARG, x: x : REP.[X], px: pred X x then Rep X (Abs X x) = x;
		apply tp_spec[OF tp_eq];
		- if 1, 2, 3, 4, 5, 6;
			by 6[OF X x px].
		.
	lemma Rep_eq_imp_Abs_eq: if [X : ARG, a : ABS X], Rep: Rep X a = x then Abs X x = a;
		fold Rep; apply Abs_Rep.

end
