---
# Extensional Function Type
---

import Quotients.

begin

definition map_eq_ = (fun ('a,'b) : TYPE × TYPE, f g : 'a ⇒ 'b. ∀x : 'a. f x = g x).

lemma map_eq__type! if ['a : TYPE, 'b : TYPE] then map_eq_ ('a,'b) : ('a ⇒ 'b) ⇒ ('a ⇒ 'b) ⇒ Prop;
	by eq_prop[of 'b] #simp map_eq__def.

lemma map_eq__elim1:
	if fg: map_eq_ ('a,'b) f g, ['a : TYPE, 'b : TYPE, f : 'a ⇒ 'b, g : 'a ⇒ 'b, x : 'a]
	then f x = g x;
	by eq_prop[of 'b] fg[simp map_eq__def, THEN all_elim1].

note map_eq__simp2: map_eq__elim1[OF > > > _].

lemma map_eq__intro:
	if all: ∀x. x : 'a ⟹ f x = g x, ['a : TYPE, 'b : TYPE, f : 'a ⇒ 'b, g : 'a ⇒ 'b]
	then map_eq_ ('a,'b) f g;
	by eq_prop[of 'b] all_intro all #simp map_eq__def.

definition map_eq = (_implicit ('a,'b) : TYPE × TYPE. 'a ⇒ 'b) map_eq_.
lemma map_eq_eq:
	if ['a : TYPE, 'b : TYPE, f : 'a ⇒ 'b, g : 'a ⇒ 'b]
	then map_eq f g = (∀x : 'a. f x = g x);
	simp map_eq_def _implicit[of ('a,'b) (('a,'b). 'a ⇒ 'b) f, simp] map_eq__def.

instance Map: QuotientType (TYPE × TYPE) (('a,'b). 'a ⇒ 'b) map_eq_;
	- if X: X : TYPE × TYPE;
		apply prod_cases[OF X];
		- if #simp X = ('a,'b), ... .
		.
	- if X: X : TYPE × TYPE;
		apply prod_cases[OF X];
		- if #simp X = ('a,'b), ...; by eq_prop[of 'b] #simp map_eq__def.
		.
	- if X: X : TYPE × TYPE;
		apply prod_cases[OF X];
		- if #simp X = ('a,'b), ...; simp;
			apply equivalence_intro symmetric_intro reflexive_intro transitive_intro;
			by map_eq__intro #simp[after 1] map_eq__elim1.
		.
	.

definition[as _to] (→) = (fun 'a 'b : TYPE. Map.Abs ('a,'b)).

definition[as _app] (⋅) = Map.rep.

lemma _app_type! if f: f : 'a → 'b, ['a : TYPE, 'b : TYPE] then (f ⋅) : 'a ⇒ 'b;
	by Map.rep_type[of ('a,'b) f, OF !, simp] f[unfold _to_def,simp] #simp _app_def.

binder λ 0 0.
syntax λ _ : _. _ := (λ_:).
definition[as _lambda] (λ_:) = (Map.abs ∘) ∘ (fun_:).

lemma _lambda_eq_abs: (λx : 'a. F.[x]) = Map.abs (fun x : 'a. F.[x]);
	simp _lambda_def.

lemma _lambda_app: for 'b if ['a : TYPE, 'b : TYPE, ∀x. x : 'a ⟹ F.[x] : 'b, x : 'a]
	then (λx : 'a. F.[x]) ⋅ x = F.[x];
	simp _lambda_eq_abs _app_def;
	have 1: map_eq_ ('a,'b) (Map.rep (Map.abs (fun x' : 'a. F.[x']))) (fun x' : 'a. F.[x']);
		by Map.rep_abs_sim[of ('a,'b)].
	.. = (fun x : 'a. F.[x]) x;
		note! Map.rep_type[of ('a,'b), OF !, for a, of a, simp].
		note! Map.abs_type[of ('a,'b), OF !, for z, of z, simp].
		by Map.rep_type map_eq__elim1[OF 1].
	simp.

lemma fun_eq_intro:
	if all: ∀x. x : 'a ⟹ f ⋅ x = g ⋅ x, f: f : 'a → 'b, g: g : 'a → 'b, ['a : TYPE, 'b : TYPE]
	then f = g;
	apply Map.eq_intro[of ('a,'b)], map_eq__intro;
	by all f[simp _to_def] f g[simp _to_def] g #simp _app_def[dual].

