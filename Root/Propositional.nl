---
# Propositional Logic
---

base Root;

---
## Axiomatization
---

fix prop; -- We axiomatize what expressions are propositions.

---
Implication will also be used for describing type constraints.
Hence, we consider implication forms a proposition if the conclusion is a proposition assuming the condition.
---
assume prop_imp_intro#intro: (P ⟹ prop Q) ⟹ prop (P ⟹ Q);

---
The universal quantifier yields a proposition if the body forms a proposition for any argument.
---
import all: Binder prop (∀);

finalize;

note #intro: all.type;

obtain true where true_intro#concl: true, [prop true] :=
	- for thesis, if assm: ∀true. true ⟹ prop true ⟹ thesis :=
		by assm(∀P. prop P ⟹ P ⟹ P);
	done;

interpret true: Member prop true :=
	- prop true :=
		done;
	done;
