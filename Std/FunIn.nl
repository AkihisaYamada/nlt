---
# Function Abstraction without Equality

This theory directly formalizes Church 1940's rule of inference
> II. To replace any part $((λx_β M_α) N_β)$ of a formula by the result of substituting 
  $N_β$ for $x_β$ throughout $M_α$, provided that the bound variables of $M_α$ are distinct both 
  from $x_β$ and from the free variables of $N_β$.
without introducing meta-equality.
---
fix (:) (fun_:).

assume funIn_app_elim: for P if P.[(fun x : A. F.[x]) s], s : A then P.[F.[s]].

begin

instance Membership (:).

lemma funIn_app_intro: for P if PFs: P.[F.[s]], s: s : A then P.[(fun x : A. F.[x]) s];
	apply funIn_app_elim[for Y, of (z. P.[z] ⟹ Y), OF _ s PFs].

lemma funIn_indep_elim: if app: P.[(fun x : A. s) t], t: t : A then P.[s];
	apply funIn_app_elim[of P, OF app t].

extend To :=
	assume fun_to#intro if ∀x. x : A ⟹ F.[x] : B then (fun x : A. F.[x]) : A → B.
begin

	lemma funIn_indep_to#intro if [s : B] then (fun x : A. s) : A → B.

end

theory FUNin :=
	fix (FUN_:).
	assume fun_FUNin#intro if ∀x. x : A ⟹ F.[x] : B.[x] then (fun x : A. F.[x]) : FUN x : A. B.[x].
	assume FUNin_elim: if f : FUN x : A. B.[x], s : A then f s : B.[s].
begin

end
