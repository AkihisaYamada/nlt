---
# Quantified Minimal Logic

In addition to Propositional minimal logic, this theory axiomatizes typed quantifiers.
---

import Prop.Minimal.

begin

---
## Universal Quantifier
---

lemma not_imp_not_all: if nax: ¬ P.[x], ! A ∈ TYPE, ! x ∈ A, ! ∀y. y ∈ A ⟹ P.[y] ∈ PROP
then ¬(∀y ∈ A. P.[y]);
	apply not_intro;
	if all: ∀y ∈ A. P.[y];
		have ax: P.[x];
			by all_elim1[OF all].
		by not_imp_false[OF nax ax].
	.

namespace iff begin
	interpret iff.
	lemma ball_cong#cong: for P
		if aa': ∀x. x ∈ A ⟹ (P.[x] ⟺ P'.[x]),
			! A ∈ TYPE,
			! ∀x. x ∈ A ⟹ P.[x] ∈ PROP,
			! ∀x. x ∈ A ⟹ P'.[x] ∈ PROP
		then (∀x ∈ A. P.[x]) ⟺ (∀x ∈ A. P'.[x]);
		apply iff_intro;
		- by all_intro #fold aa' #elim all_elim.
		- by all_intro #unfold aa' #elim all_elim.
		.
end

note #cong: iff.ball_cong.

---
## Existence
---

context iff begin
	lemma ex_cong#cong: for P
	if aa': ∀x. x ∈ A ⟹ (P.[x] ⟺ P'.[x]),
		! A ∈ TYPE,
		! ∀x. x ∈ A ⟹ P.[x] ∈ PROP,
		! ∀x. x ∈ A ⟹ P'.[x] ∈ PROP
	then (∃x ∈ A. P.[x]) ⟺ (∃x ∈ A. P'.[x]);
		apply iff_intro;
		if ex;
			apply ex_intro;
			for Q if assm, !;
				apply ex_elim[OF ex];
				for x if !;
					unfold aa';
					apply assm!1.
				.
			.
		if ex;
			apply ex_intro;
			for Q if assm, !;
				apply ex_elim[OF ex];
				for x if !;
					fold aa';
					apply assm!1.
				.
			.
		.
end

note #cong: iff.ex_cong.

lemma nex_false: if ! A ∈ TYPE then ¬(∃x ∈ A. false);
	by not_intro #elim ex_elim.

lemma all_imp_iff_ex:
if ! A ∈ TYPE, ! Q ∈ PROP, ! ∀x. x ∈ A ⟹ P.[x] ∈ PROP
then (∀x ∈ A. P.[x] ⟹ Q) ⟺ (∃x ∈ A. P.[x]) ⟹ Q;
	apply iff_intro;
	if imp: ∀x ∈ A. P.[x] ⟹ Q, ex: ∃x ∈ A. P.[x];
		apply ex_elim[OF ex];
		for x if ! x ∈ A, ax: P.[x];
			by all_elim1[OF imp, of x] ax.
		.
	if imp: (∃x ∈ A. P.[x]) ⟹ Q;
		apply all_intro;
		for x if !, ax: P.[x];
			by imp ex_intro1[OF ax].
		.
	.


---
## Double negation and universal quantification.

The following direction is provable in general, but the opposite direction requires something similar to the axiom of choice.
---
lemma nnall_imp:
if nnall: ¬¬(∀x ∈ A. P.[x]), ! A ∈ TYPE, ! ∀x. x ∈ A ⟹ P.[x] ∈ PROP
then ∀x ∈ A. ¬¬P.[x];
	apply all_intro;
	for x if !;
		apply not_intro;
		if nax: ¬P.[x];
			by not_imp_false[OF nnall] not_imp_not_all[OF nax].
		.
	.

---
The other direction is provable if inside the quantification has negation.
---

lemma nex_iff_all_not:
if ! A ∈ TYPE, ! ∀x. x ∈ A ⟹ P.[x] ∈ PROP
then ¬(∃x ∈ A. P.[x]) ⟺ (∀x ∈ A. ¬P.[x]);
	unfold+ not_iff_imp_false;
	fold all_imp_iff_ex.

lemma nnall_not_iff:
if ! A ∈ TYPE, ! ∀x. x ∈ A ⟹ P.[x] ∈ PROP
then ¬¬(∀x ∈ A. ¬P.[x]) ⟺ (∀x ∈ A. ¬P.[x]);
	fold+ nex_iff_all_not;
	by nnnot_iff.
