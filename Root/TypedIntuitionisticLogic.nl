------
# Typed Intuitionistic Logic
------

base Root;

import TypedMinimalLogic;
import PropositionalIntuitionistic;

begin

setup rewrite iff_imp iff_imp_rev iff.refl iff.trans;
setup dual iff.sym;
