---
# Propositional Logic
---

base Root;

---
## Axiomatization
---

fix prop; -- We axiomatize what expressions are propositions.

assume prop_prop#concl: prop (prop x);

---
Implication yields a proposition, if the condition is a proposition and so is the conclusion whenever the condition holds.
---
assume prop_imp_intro#intro: prop P ⟹ (P ⟹ prop Q) ⟹ prop (P ⟹ Q);

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
	end;
