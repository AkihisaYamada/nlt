---
# Quantified Minimal Logic

In addition to Propositional minimal logic, this theory axiomatizes typed quantifiers.
---

fix false (¬) (∧) (∨) (⟺) (∀∋) (∃∋).

import ..Minimal.

assume all_type!
if A ∈ TYPE, ∀x. x ∈ A ⟹ P.[x] ∈ PROP then (∀x ∈ A. P.[x]) ∈ PROP.

assume all_intro:
if ∀x. x ∈ A ⟹ P.[x], A ∈ TYPE, ∀x. x ∈ A ⟹ P.[x] ∈ PROP
then ∀x ∈ A. P.[x].

assume all_elim1: for x
if ∀y ∈ A. P.[y], A ∈ TYPE, ∀y. y ∈ A ⟹ P.[y] ∈ PROP, x ∈ A
then P.[x].

assume ex_type!
if A ∈ TYPE, ∀x. x ∈ A ⟹ P.[x] ∈ PROP then (∃x ∈ A. P.[x]) ∈ PROP.

assume ex_intro1: for x,
if P.[x], A ∈ TYPE, x ∈ A, ∀y. y ∈ A ⟹ P.[y] ∈ PROP
then ∃y ∈ A. P.[y].

assume ex_elim:
if ∃x ∈ A. P.[x]
then ∀Q. (∀x. P.[x] ⟹ x ∈ A ⟹ Q) ⟹ A ∈ TYPE ⟹ (∀x. x ∈ A ⟹ P.[x] ∈ PROP) ⟹ Q ∈ PROP ⟹ Q.

begin

---
## Universal Quantifier
---
lemma all_elim:
	if all: ∀x ∈ A. P.[x]
	then ∀Q. ((∀x. x ∈ A ⟹ P.[x]) ⟹ Q) ⟹ A ∈ TYPE ⟹ (∀y. y ∈ A ⟹ P.[y] ∈ PROP) ⟹ Q;
	for Q if assm, !, !;
		apply assm;
		for x if !;
			apply all_elim1[OF all, of x].
		.
	.

lemma not_imp_not_all: if nax: ¬ P.[x], ! A ∈ TYPE, ! x ∈ A, ! ∀y. y ∈ A ⟹ P.[y] ∈ PROP
then ¬(∀y ∈ A. P.[y]);
	apply not_intro;
	if all: ∀y ∈ A. P.[y];
		have ax: P.[x];
			by all_elim1[OF all].
		by not_imp_false[OF nax ax].
	.

lemma tall_cong#cong: for P
	if aa': ∀x. x ∈ A ⟹ (P.[x] ⟺ P'.[x]),
		! A ∈ TYPE,
		! ∀x. x ∈ A ⟹ P.[x] ∈ PROP,
		! ∀x. x ∈ A ⟹ P'.[x] ∈ PROP
	then (∀x ∈ A. P.[x]) ⟺ (∀x ∈ A. P'.[x]);
	apply iff_intro;
	- by all_intro #fold aa' #elim all_elim.
	- by all_intro #unfold aa' #elim all_elim.
	.

---
## Existence
---

lemma ex_intro:
if assm: ∀Q. (∀x. P.[x] ⟹ x ∈ A ⟹ Q) ⟹ Q ∈ PROP ⟹ Q,
	! A ∈ TYPE,
	! ∀x. x ∈ A ⟹ P.[x] ∈ PROP
then ∃x ∈ A. P.[x];
	apply assm;
	for x;
		by ex_intro1[of x].
	.

lemma ex_iff:
if ! A ∈ TYPE, ! ∀x. x ∈ A ⟹ P.[x] ∈ PROP
then (∃x ∈ A. P.[x]) ⟺ (∀Q ∈ PROP. (∀x ∈ A. P.[x] ⟹ Q) ⟹ Q);
	apply iff_intro;
	if ex: ∃x ∈ A. P.[x];
		apply ex_elim[OF ex];
		for x if !P.[x], !;
			apply all_intro;
			for Q if !, all: ∀x ∈ A. P.[x] ⟹ Q;
				by all_elim1[of x, OF all].
			.
		.
	if all: ∀Q ∈ PROP. (∀x ∈ A. (P.[x] ⟹ Q)) ⟹ Q;
		apply all_elim1[OF all];
		- .
		- .
		apply all_intro;
		for x; by ex_intro1[of x].
		.
	.

lemma ex_cong#cong: for P
if aa': ∀x. x ∈ A ⟹ (P.[x] ⟺ P'.[x]),
	! A ∈ TYPE,
	! ∀x. x ∈ A ⟹ P.[x] ∈ PROP,
	! ∀x. x ∈ A ⟹ P'.[x] ∈ PROP
then (∃x ∈ A. P.[x]) ⟺ (∃x ∈ A. P'.[x]);
	unfold ex_iff aa'.

lemma ex_imp_all_imp:
if ex: ∃x ∈ A. P.[x] ⟹ Q, all: ∀x ∈ A. P.[x],
	! A ∈ TYPE, ! Q ∈ PROP, ! ∀x. x ∈ A ⟹ P.[x] ∈ PROP
then Q;
	apply ex_elim[OF ex];
	for x if imp: P.[x] ⟹ Q, ! x ∈ A;
		by imp all_elim1[OF all].
	.

lemma all_imp_iff_ex:
if ! A ∈ TYPE, ! Q ∈ PROP, ! ∀x. x ∈ A ⟹ P.[x] ∈ PROP
then (∀x ∈ A. P.[x] ⟹ Q) ⟺ (∃x ∈ A. P.[x]) ⟹ Q;
	apply iff_intro;
	if imp: ∀x ∈ A. P.[x] ⟹ Q, ex: ∃x ∈ A. P.[x];
		apply ex_elim[OF ex];
		for x if ax: P.[x], ! x ∈ A;
			by all_elim1[OF imp, of x] ax.
		.
	if imp: (∃x ∈ A. P.[x]) ⟹ Q;
		apply all_intro;
		for x if !, ax: P.[x];
			by imp ex_intro1[OF ax].
		.
	.

lemma nex_false: if ! A ∈ TYPE then ¬(∃x ∈ A. false);
	by not_intro #elim ex_elim.


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
if ! A ∈ PROP, ! ∀x. x ∈ A ⟹ P.[x] ∈ PROP
then ¬(∃x ∈ A. P.[x]) ⟺ (∀x ∈ A. ¬P.[x]);
	unfold+ not_iff_imp_false;
	fold all_imp_iff_ex.

lemma nnall_not_iff:
if ! A ∈ PROP, ! ∀x. x ∈ A ⟹ P.[x] ∈ PROP
then ¬¬(∀x ∈ A. ¬P.[x]) ⟺ (∀x ∈ A. ¬P.[x]);
	fold+ nex_iff_all_not;
	by nnnot_iff.
