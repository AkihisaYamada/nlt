fix (¬).
import not: Unary (¬) Prop Prop.
import Imp.
begin

note! not.closed.

extend Membership begin

	theory Irreflexive A (⊏) :=
		import Relation A (⊏).
		assume irrefl: if x ∈ A then ¬ x ⊏ x.
	end

	theory Asymmetric A (⊏) :=
		import Relation A (⊏).
		assume asym: if x ⊏ y, x ∈ A, y ∈ A then ¬ y ⊏ x.
	end

end

theory ContraPos := -- @Latin modus tollens
	assume not_imp_imp_not: if ¬Q, P ⟹ Q, P : Prop, Q : Prop then ¬P.
begin

	instance not: Antitone (¬) Prop (⟹) (⟹);
		- if PQ: P ⟹ Q, ...; by not_imp_imp_not[OF _ PQ].
		.

	lemma not_elim_not: if nP: ¬P, P: P, [P : Prop, Q : Prop] then ¬Q;
		by not_imp_imp_not[OF nP] P.

	lemma nimp_intro: if P: P, nQ: ¬Q, [P : Prop, Q : Prop] then ¬(P ⟶ Q);
		apply not_imp_imp_not[OF nQ];
		- if PQ then Q;
			by PQ[THEN imp_elim1] P.
		.
	lemma nimp_imp_imp: if imp: ¬(P ⟶ Q) ⟹ R, [P : Prop, Q : Prop] then P ⟹ ¬Q ⟹ R;
		by imp nimp_intro.

	lemma nimp_elim2: if nimp: ¬(P ⟶ Q), [P : Prop, Q : Prop] then ¬Q;
		apply not_imp_imp_not[OF nimp].

	lemma nimp_not_elim1: if nimpn: ¬(P ⟶ ¬Q), [P : Prop, Q : Prop] then ¬ ¬ P;
		apply not_imp_imp_not[OF nimpn];
		- if nP; apply imp_intro; by not_elim_not[OF nP].
		.

	lemma nimp_not_elim: if nimp: ¬(P ⟶ ¬Q), imp: ¬ ¬ P ⟹ ¬ ¬ Q ⟹ R, [P : Prop, Q : Prop] then R;
		apply imp;
		by nimp_elim2[OF nimp] nimp_not_elim1[OF nimp].

---
	lemma nall_intro1: for x if nPx: ¬ P.[x] then ¬(∀y. P.[y]);
		apply not_imp_imp_not[OF nPx].

	lemma nall_intro: if assm: ∀Q. (∀x. ¬ P.[x] ⟹ Q) ⟹ Q then ¬(∀y. P.[y]);
		apply assm;
		by #elim nall_intro1.

	lemma nall_elim_not: if nall: ¬(∀x. P.[x]), QP: Q ⟹ ∀x. P.[x] then ¬Q;
		apply not_imp_imp_not[OF nall]; by QP.


	lemma nnall_imp: if nnall: ¬ ¬ (∀x. P.[x]) then ∀x. ¬ ¬ P.[x];
		by not_imp_imp_not[OF nnall nall_intro1].

	-- If there is anything negated, then the theory is not inconsistent.
	lemma not_imp_not_inconsistent: if nP: ¬P then ¬(∀Q. Q);
		apply not_imp_imp_not[OF nP].

	-- And if it is not inconsistent, explosive statements are negated.
	extend NotInconsistent begin

		instance NotExplosive;
			- if P0: P ⟹ ∀Q. Q then ¬P;
				apply not.cmono[OF P0 not_inconsistent].
			.

	end
---

	lemma not_imp_not_true: if nP: ¬P, P: P, [P : Prop] then ¬true;
		by not_elim_not[OF nP P].

	lemma not_true_imp_not: if nt: ¬true, [P : Prop] then ¬P;
		apply not_elim_not[OF nt].

	extend Membership begin

		theory Order A (⊏) :=
			import Irreflexive A (⊏), Transitive A (⊏).
		begin
			instance Asymmetric A (⊏);
				- for x y if xy: x ⊏ y, ... then ¬ y ⊏ x;
					apply not_imp_imp_not[OF irrefl[of x, OF !]];
					- if yx: y ⊏ x then x ⊏ x;
						by trans[OF xy yx].
					.
				.
		end

	end

	extend AllRelStrict begin

		lemma nall_intro1: for x
			if nPx: ¬ P.[x], [x ⊏ a, a : A, ∀y. y ⊏ a ⟹ P.[y] : Prop]
			then ¬(∀x ⊏ a. P.[x]);
			apply not_imp_imp_not[OF nPx];
			- if all: ∀x ⊏ a. P.[x];
				apply all_elim1[OF all].
			.
		lemma nall_intro:
			if assm: ∀Q. (∀x. ¬ P.[x] ⟹ x ⊏ a ⟹ Q) ⟹ Q,
			   [a : A, ∀y. y ⊏ a ⟹ P.[y] : Prop]
			then ¬(∀x ⊏ a. P.[x]);
			apply assm;
			- for x;
				by nall_intro1[of x].
			.

		lemma nnall_imp:
			if nnall: ¬ ¬ (∀x ⊏ a. P.[x]), [a : A, ∀y. y ⊏ a ⟹ P.[y] : Prop]
			then ∀x ⊏ a. ¬ ¬ P.[x];
			apply all_intro;
			- if xa! x ⊏ a;
				apply not_imp_imp_not[OF nnall];
				by nall_intro1[OF _ xa].
			.

	end

	extend ExRelStrict begin

		lemma nex_elim1:
			if nex: ¬(∃x ⊏ a. P.[x]), xa! x ⊏ a, [a : A, ∀y. y ⊏ a ⟹ P.[y] : Prop]
			then ¬ P.[x];
			apply not_imp_imp_not[OF nex]; by ex_intro1[OF _ xa].

		lemma nex_elim:
			if nex: ¬(∃x ⊏ a. P.[x]), assm: (∀x. x ⊏ a ⟹ ¬ P.[x]) ⟹ Q,
			   [a : A, ∀y. y ⊏ a ⟹ P.[y] : Prop]
			then Q;
			apply assm;
			- for x;
				by nex_elim1[OF nex, of x].
			.

	end

end

theory NotExplosive :=
	assume not_intro_inconsistent: if P ⟹ ∀Q. Q : Prop ⟹ Q, P : Prop then ¬P.
begin

	lemma not_false! ¬false;
		apply not_intro_inconsistent; by #elim false_elim.

	lemma not_intro: if P0: P ⟹ false, [P : Prop] then ¬P;
		apply not_intro_inconsistent; by #elim P0 false_elim.


end

theory SelfRefutation :=
	assume imp_not_imp_not: if P ⟹ ¬P, P : Prop then ¬P.
begin

	instance NotExplosive;
		- for P if nP, ...;
			apply imp_not_imp_not;
			by #elim nP.
		.

end

theory ExplosiveNot :=
	assume not_elim: if ¬P, P, P : Prop, Q : Prop then Q.
begin

	lemma not_imp_false: if nP: ¬P, P: P, [P : Prop] then false;
		apply not_elim[OF nP P].

end

theory NNotElim :=
	assume nnot_elim:-- @English Double Negation Elimination
		if ¬ ¬ P, P : Prop then P.
end

theory ClaviusLaw :=
	assume not_imp_imp:
		-- @English Clavius's Law
		-- @Latin Consequentia Mirabilis
		if ¬P ⟹ P, P : Prop then P.

end

theory ExcludedMiddle :=
	assume cases: if P ⟹ Q, ¬P ⟹ Q, P : Prop, Q : Prop then Q.
begin

	instance ClaviusLaw;
		- if nPP: ¬P ⟹ P, ... then P;
			by cases[OF _ nPP].
		.

	instance SelfRefutation;
		- if PnP: P ⟹ ¬P, ... then ¬P;
			by cases[OF PnP].
		.

	lemma not_imp_elim:
		if nPQ: ¬P ⟹ Q, PR: P ⟹ R, QR: Q ⟹ R, [P : Prop, Q : Prop, R : Prop] then R;
		apply cases[of P];
		- by PR.
		- by nPQ QR.
		.
		
end
