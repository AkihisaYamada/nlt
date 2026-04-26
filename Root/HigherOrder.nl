import Membership.
import FunType.
import FirstOrder.

assume fun_type: if A ∈ QTYPE, B ∈ QTYPE then A → B ∈ QTYPE.

begin

interpret SecondOrder;
	instantiate IND := QTYPE.
	by fun_type.
end

