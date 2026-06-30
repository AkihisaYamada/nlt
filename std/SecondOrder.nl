import Fun.
import FirstOrder.
fix IND.
assume IND_type: if A ∈ IND then A ∈ QTYPE.
assume IND_fun_type: if A ∈ IND, B ∈ QTYPE then A → B ∈ QTYPE.

end
