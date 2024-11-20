base Root;

import MinimalLogic;

infix → 61 60 60;
infix : 31 30 30;
fix Prop : →;

assume fun_type: f : A → B ⟹ a : A ⟹ f a : B;

assume excluded_middle: P : Prop ⟹ P ∨ ¬P;
assume true_type: true : Prop;
assume false_type: false : Prop;
assume imp_type: (⟹) : Prop → Prop → Prop;
assume and_type: (∧) : Prop → Prop → Prop;
assume or_type: (∨) : Prop → Prop → Prop;
assume not_type: (¬) : Prop → Prop;
assume all_type: (∀x. α.[x] : Prop) ⟹ (∀x. α.[x]) : Prop;

