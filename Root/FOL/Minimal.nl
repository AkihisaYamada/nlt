---
# Quantified Minimal Logic

In addition to Propositional minimal logic, this theory axiomatizes typed quantifiers.
---

import Prop.Minimal.

begin

---
## Universal Quantifier
---

lemma not_imp_not_all:
	if nax: ¬ P.[x], ! A ∈ QTYPE, ! x ∈ A, ! ∀y. y ∈ A ⟹ P.[y] ∈ Prop
	then ¬(∀y ∈ A. P.[y]);
apply not.intro;
- if all: ∀y ∈ A. P.[y];
	have ax: P.[x];
		by all.elim1[OF all].
	by not_imp_false[OF nax ax].
.

namespace iff:
	interpret iff.
	lemma all_cong: for P
		if aa': ∀x. x ∈ A ⟹ (P.[x] ⟺ P'.[x]),
			! A ∈ QTYPE,
			! ∀x. x ∈ A ⟹ P.[x] ∈ Prop,
			! ∀x. x ∈ A ⟹ P'.[x] ∈ Prop
		then (∀x ∈ A. P.[x]) ⟺ (∀x ∈ A. P'.[x]);
	apply iff.intro;
	-; by all.intro #fold aa' #elim all.elim.
	-; by all.intro #unfold aa' #elim all.elim.
	.
end

note(cong) iff.all_cong.

---
## Existence
---

context iff begin
	lemma ex_cong: for P
		if aa': ∀x. x ∈ A ⟹ (P.[x] ⟺ P'.[x]),
			! A ∈ QTYPE,
			! ∀x. x ∈ A ⟹ P.[x] ∈ Prop,
			! ∀x. x ∈ A ⟹ P'.[x] ∈ Prop
		then (∃x ∈ A. P.[x]) ⟺ (∃x ∈ A. P'.[x]);
	apply iff.intro;
	- if ex;
		apply ex.intro;
		- for Q if assm, !;
			apply ex.elim[OF ex];
			- for x if Px, !;
				by assm[of x] Px #fold aa'.
			.
		.
	- if ex;
		apply ex.intro;
		- for Q if assm, !;
			apply ex.elim[OF ex];
			- for x if P'x, !;
				by assm[of x] P'x #unfold aa'.
			.
		.
	.
end

note(cong) iff.ex_cong.

lemma nex_false: if ! A ∈ QTYPE then ¬(∃x ∈ A. false);
by not.intro #elim ex.elim.

lemma all_imp_iff_ex:
	if ! A ∈ QTYPE, ! Q ∈ Prop, ! ∀x. x ∈ A ⟹ P.[x] ∈ Prop
	then (∀x ∈ A. P.[x] ⟹ Q) ⟺ (∃x ∈ A. P.[x]) ⟹ Q;
apply iff.intro;
- if imp: ∀x ∈ A. P.[x] ⟹ Q, ex: ∃x ∈ A. P.[x];
	apply ex.elim[OF ex];
	- for x if !x ∈ A, ax: P.[x];
		by all.elim1[OF imp, of x] ax.
	.
- if imp: (∃x ∈ A. P.[x]) ⟹ Q;
	apply all.intro;
	- for x if !, ax: P.[x];
		by imp ex.intro1[OF ax].
	.
.


---
## Double negation and universal quantification.

The following direction is provable in general, but the opposite direction requires something similar to the axiom of choice.
---
lemma nnall_imp:
	if nnall: ¬¬(∀x ∈ A. P.[x]), ! A ∈ QTYPE, ! ∀x. x ∈ A ⟹ P.[x] ∈ Prop
	then ∀x ∈ A. ¬¬P.[x];
apply all.intro;
- for x if !;
	apply not.intro;
	- if nax: ¬P.[x];
		by not_imp_false[OF nnall] not_imp_not_all[OF nax].
	.
.

---
The other direction is provable if inside the quantification has negation.
---

lemma nex_iff_all_not:
	if ! A ∈ QTYPE, ! ∀x. x ∈ A ⟹ P.[x] ∈ Prop
	then ¬(∃x ∈ A. P.[x]) ⟺ (∀x ∈ A. ¬P.[x]);
unfold not_iff_imp_false;
fold all_imp_iff_ex.

lemma nnall_not_iff:
	if ! A ∈ QTYPE, ! ∀x. x ∈ A ⟹ P.[x] ∈ Prop
	then ¬¬(∀x ∈ A. ¬P.[x]) ⟺ (∀x ∈ A. ¬P.[x]);
fold nex_iff_all_not;
by nnnot_iff.

end
