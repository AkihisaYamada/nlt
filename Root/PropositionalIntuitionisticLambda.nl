import PropositionalMinimalLambda.
import PropositionalIntuitionistic.

begin

setup rewrite iff_imp iff_imp_rev iff.refl iff.trans.
setup dual iff.sym.

setup rewrite eq_imp eq_imp_rev eq.refl eq.trans.
setup dual eq.sym.

setup define beta.

