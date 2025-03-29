import PropositionalMinimal.

import TypedForAll.

import TypedExists.

begin

setup rewrite iff_imp iff_imp_rev iff.refl iff.trans.
setup dual iff.sym.

note! all.type.
note! ex.type.

lemma all_elim:
	if all: ∀x:ι. α.[x]
	then ∀P. ((∀x. ι x ⟹ α.[x]) ⟹ P) ⟹ (∀y. ι y ⟹ prop α.[y]) ⟹ P;
	- for P, if assm:, !;
		apply assm,
		- for x, if !;
			apply all_elim1[OF all](x).
		.
	.

lemma not_imp_not_all: if nax: ¬α.[x], ! ι x, ! ∀y. ι y ⟹ prop α.[y] then
	¬(∀y:ι. α.[y]);
	apply not_intro,
	- if all: ∀y:ι. α.[y];
		have ax: α.[x];
			by all_elim1[OF all].
		by not_imp_false[OF nax ax].
	.

lemma tall_cong#cong: for α,
	if aa': ∀x. ι x ⟹ (α.[x] ⟺ α'.[x]),
		! ∀x. ι x ⟹ prop α.[x],
		! ∀x. ι x ⟹ prop α'.[x]
	then (∀x:ι. α.[x]) ⟺ (∀x:ι. α'.[x]);
	apply iff_intro,
	- by all_intro #fold aa' #elim all_elim.
	- by all_intro #unfold aa' #elim all_elim.
	.

---
### Existence
---

lemma ex_intro:
	if assm: ∀P. (∀x. α.[x] ⟹ ι x ⟹ P) ⟹ prop P ⟹ P,
		! ∀x. ι x ⟹ prop α.[x]
	then ∃x:ι. α.[x];
	apply assm,
	- for x;
		by ex_intro1(x).
	.

lemma ex_iff: if ! ∀x. ι x ⟹ prop α.[x] then
	(∃x:ι. α.[x]) ⟺ (∀P:prop. (∀x:ι. α.[x] ⟹ P) ⟹ P);
	apply iff_intro,
	- if ex: ∃x:ι. α.[x];
		apply ex_elim[OF ex],
		- for x, if !α.[x], !;
			apply all_intro,
			- for P, if !, all: ∀x:ι. α.[x] ⟹ P;
				by all_elim1(x)[OF all].
			.
		.
	- if all: ∀P:prop. (∀x:ι. (α.[x] ⟹ P)) ⟹ P;
		apply all_elim1[OF all],
		- .
		- .
		apply all_intro,
		- for x; by ex_intro1(x).
		.
	.

lemma ex_imp_all_imp:
	if ex: ∃x:ι. α.[x] ⟹ P, all: ∀x:ι. α.[x], ! prop P, ! ∀x. ι x ⟹ prop α.[x]
	then P;
	apply ex_elim[OF ex],
	- for x, if imp: α.[x] ⟹ P, ! ι x;
		by imp all_elim1[OF all].
	.

lemma all_imp_iff_ex: if ! prop P, ! ∀x. ι x ⟹ prop α.[x] then
	(∀x:ι. α.[x] ⟹ P) ⟺ (∃x:ι. α.[x]) ⟹ P;
	apply iff_intro,
	- if imp: ∀x:ι. α.[x] ⟹ P, ex: ∃x:ι. α.[x];
		obtain x where ax: α.[x], ! ι x;
			- for thesis, if assm:;
				by ex_elim[OF ex assm].
			.
		by all_elim1[OF imp](x) ax.
	- if imp: (∃x:ι. α.[x]) ⟹ P;
		apply all_intro,
		- for x, if !, ax: α.[x];
			by imp ex_intro1[OF ax].
		.
	.


---
## Double negation and universal quantification.

The following direction is provable in general, but the opposite direction requires something similar to the axiom of choice.
---
lemma nnall_imp:
	if nnall: ¬¬(∀x:ι. α.[x]), ! ∀x. ι x ⟹ prop α.[x]
	then (∀x:ι. ¬¬α.[x]);
	apply all_intro,
	- for x, if !;
		apply not_intro,
		- if nax: ¬α.[x];
			by not_imp_false[OF nnall] not_imp_not_all[OF nax].
		.
	.

---
The other direction is provable if inside the quantification has negation.
---

lemma nex_iff_all_not: if ! ∀x. ι x ⟹ prop α.[x] then
	¬(∃x:ι. α.[x]) ⟺ (∀x:ι. ¬α.[x]);
	unfold+ not_iff_imp_false,
	fold all_imp_iff_ex.

lemma nnall_not_iff: if ! ∀x. ι x ⟹ prop α.[x] then
	¬¬(∀x:ι. ¬α.[x]) ⟺ (∀x:ι. ¬α.[x]);
	fold+ nex_iff_all_not,
	by nnnot_iff.

