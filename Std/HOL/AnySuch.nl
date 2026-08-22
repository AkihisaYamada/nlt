---
# Hilbert's Choice Operator
---
import SuchSignature.
assume any_such_axiom: if 'a : TYPE then ∀P : 'a → Prop. ∀x : 'a. P x ⟶ P (SUCH 'a P).

begin

instance Prop.AnySuchTyped TYPE;
	note#cong eq_cong_meta.
	- for x if Px: P.[x] for 'a if ...;
		define f = (fun z : 'a. P.[z]).
		have fS: f (SUCH 'a f);
			apply any_such_axiom[of 'a, THEN all_elim1[of f], THEN all_elim1[of x], THEN imp_elim1];
			by Px #simp f_def.
		by fS[simp f_def] #simp such_def.
	.
