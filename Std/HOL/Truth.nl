---
# Truth Values

Gordon's HOL uses type `bool` for propositions and assumes that true and false are the only inhabitants.
However, mathematicians do distinguish theorem statements rather than identifying them with `true`.
Therefore we introduce `Truth` values, which are `Prop` quotiented by `⟷`.
In classical logic, `Truth` behave exactly as `bool` of HOL.
---
import Quotients.

begin

instance Truth: QuotientType TYPE (x. Prop) (fun _ : TYPE. (⟷));
	-.
	-.
	- if ['X : TYPE]; by iff.equivalence.
	.

definition Truth = Truth.Abs Prop.
definition truth_of = (fun p : Prop. Truth.abs p).
definition is_true = (fun b : Truth. Truth.rep b).

definition True = truth_of true.
definition False = truth_of false.

lemma Truth_TYPE! Truth : TYPE; by Truth.Abs_type1 #simp Truth_def.

lemma truth_of_type! truth_of : Prop ⇒ Truth;
	by Truth.abs_type[of Prop] #simp truth_of_def Truth_def.
note truth_of_type1! truth_of_type[THEN to_elim1].

lemma is_true_type! is_true : Truth ⇒ Prop;
	by Truth.rep_type[of Prop] #simp is_true_def Truth_def.
note is_true_type1! is_true_type[THEN to_elim1].

lemma True_type! True : Truth; simp True_def.
lemma False_type! False : Truth; simp False_def.

lemma truth_of_cong:
	if iff: p ⟷ q, [p : Prop, q : Prop] then truth_of p = truth_of q;
-	note 1: Truth.rep_abs_sim[for a, of Prop a, simp].
	simp truth_of_def;
	apply Truth.eq_intro[of Prop]; simp;
	.. ⟷ p; apply 1.
	.. ⟷ q; apply iff.
	by 1[dual] Truth.rep_type[of Prop] Truth.abs_type[of Prop].
.

lemma truth_of_eq_True:
	if p: p, [p : Prop] then truth_of p = True;
	unfold True_def; apply truth_of_cong; by iff_true p.

lemma truth_of_eq_truth_of_elim: if eq: truth_of p = truth_of q, [p : Prop, q : Prop] then p ⟷ q;
	apply Truth.abs_eq_elim[for x y, of Prop x y, simp];
	apply eq[simp truth_of_def].

lemma is_true_truth_of_iff#simp if [p : Prop] then is_true (truth_of p) ⟷ p;
	simp is_true_def; simp truth_of_def;
	apply Truth.rep_abs_sim[of Prop p, simp].

lemma is_true_truth_of_elim1: if p: is_true (truth_of p), [p : Prop] then p;
	fold[on (⟷)] is_true_truth_of_iff; apply p.

lemma True_is_true! is_true True;
	unfold True_def; unfold[on (⟷)] is_true_truth_of_iff.

instance Truth: Std.Prop Truth (:) (⇒);
	- apply to_elim1=.
	.
