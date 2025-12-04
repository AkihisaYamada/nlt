---
# Quantified Minimal Logic

In addition to propositional minimal logic, this theory axiomatizes typed quantifiers.
Now the true proposition can be obtained using the universal quantifier.
---
import Base.

fix (:) prop false (¬) (∧) (∨) (⟺) (∀:) (∃:).

import TypedAll.
import MinimalPL.

assume ex_type! (∀x. x : ι ⟹ α.[x] : prop) ⟹ (∃x : ι. α.[x]) : prop.
assume ex_intro1: for x, α.[x] ⟹ x : ι ⟹ (∀y. y : ι ⟹ α.[y] : prop) ⟹ ∃y:ι. α.[y].
assume ex_elim: (∃x:ι. α.[x]) ⟹ ∀P. (∀x. α.[x] ⟹ x : ι ⟹ P) ⟹
	(∀x. x : ι ⟹ α.[x] : prop) ⟹ P : prop ⟹ P.

begin

---
## Universal Quantifier
---

lemma not_imp_not_all: if nax: ¬α.[x], ! x : ι, ! ∀y. y : ι ⟹ α.[y] : prop then
	¬(∀y:ι. α.[y]);
	apply not_intro;
	if all: ∀y:ι. α.[y];
		have ax: α.[x];
			by all_elim1[OF all].
		by not_imp_false[OF nax ax].
	.

lemma tall_cong#cong: for α
	if aa': ∀x. x : ι ⟹ (α.[x] ⟺ α'.[x]),
		! ∀x. x : ι ⟹ α.[x] : prop,
		! ∀x. x : ι ⟹ α'.[x] : prop
	then (∀x:ι. α.[x]) ⟺ (∀x:ι. α'.[x]);
	apply iff_intro;
	- by all_intro #fold aa' #elim all_elim.
	- by all_intro #unfold aa' #elim all_elim.
	.

---
## Existence
---

lemma ex_intro:
	if assm: ∀P. (∀x. α.[x] ⟹ x : ι ⟹ P) ⟹ P : prop ⟹ P,
		! ∀x. x : ι ⟹ α.[x] : prop
	then ∃x:ι. α.[x];
	apply assm;
	for x;
		by ex_intro1[of x].
	.

lemma ex_iff: if ! ∀x. x : ι ⟹ α.[x] : prop then
	(∃x:ι. α.[x]) ⟺ (∀P:prop. (∀x:ι. α.[x] ⟹ P) ⟹ P);
	apply iff_intro;
	if ex: ∃x:ι. α.[x];
		apply ex_elim[OF ex];
		for x if !α.[x], !;
			apply all_intro;
			for P if !, all: ∀x:ι. α.[x] ⟹ P;
				by all_elim1[of x, OF all].
			.
		.
	if all: ∀P:prop. (∀x:ι. (α.[x] ⟹ P)) ⟹ P;
		apply all_elim1[OF all];
		- .
		- .
		apply all_intro;
		for x; by ex_intro1[of x].
		.
	.

lemma ex_cong#cong: for α
	if aa': ∀x. x : ι ⟹ (α.[x] ⟺ α'.[x]),
		! ∀x. x : ι ⟹ α.[x] : prop,
		! ∀x. x : ι ⟹ α'.[x] : prop
	then (∃x:ι. α.[x]) ⟺ (∃x:ι. α'.[x]);
	unfold ex_iff aa'.

lemma ex_imp_all_imp:
	if ex: ∃x:ι. α.[x] ⟹ P, all: ∀x:ι. α.[x], ! P : prop, ! ∀x. x : ι ⟹ α.[x] : prop
	then P;
	apply ex_elim[OF ex];
	for x if imp: α.[x] ⟹ P, ! x : ι;
		by imp all_elim1[OF all].
	.

lemma all_imp_iff_ex: if ! P : prop, ! ∀x. x : ι ⟹ α.[x] : prop then
	(∀x:ι. α.[x] ⟹ P) ⟺ (∃x:ι. α.[x]) ⟹ P;
	apply iff_intro;
	if imp: ∀x:ι. α.[x] ⟹ P, ex: ∃x:ι. α.[x];
		apply ex_elim[OF ex];
		for x if ax: α.[x], ! x : ι;
			by all_elim1[OF imp, of x] ax.
		.
	if imp: (∃x:ι. α.[x]) ⟹ P;
		apply all_intro;
		for x if !, ax: α.[x];
			by imp ex_intro1[OF ax].
		.
	.

lemma nex_false: ¬(∃x:ι. false);
	by not_intro #elim ex_elim.


---
## Double negation and universal quantification.

The following direction is provable in general, but the opposite direction requires something similar to the axiom of choice.
---
lemma nnall_imp:
	if nnall: ¬¬(∀x:ι. α.[x]), ! ∀x. x : ι ⟹ α.[x] : prop
	then ∀x:ι. ¬¬α.[x];
	apply all_intro;
	for x if !;
		apply not_intro;
		if nax: ¬α.[x];
			by not_imp_false[OF nnall] not_imp_not_all[OF nax].
		.
	.

---
The other direction is provable if inside the quantification has negation.
---

lemma nex_iff_all_not: if ! ∀x. x : ι ⟹ α.[x] : prop then
	¬(∃x:ι. α.[x]) ⟺ (∀x:ι. ¬α.[x]);
	unfold+ not_iff_imp_false;
	fold all_imp_iff_ex.

lemma nnall_not_iff: if ! ∀x. x : ι ⟹ α.[x] : prop then
	¬¬(∀x:ι. ¬α.[x]) ⟺ (∀x:ι. ¬α.[x]);
	fold+ nex_iff_all_not;
	by nnnot_iff.
