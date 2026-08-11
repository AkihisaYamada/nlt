import Std, Eq, Typed, Nat.

lemma: 100 + 30 = 130.
lemma: 1000 + 300 = 1300.
lemma: 10000 + 3000 = 13000.

lemma: 1000 * 30 = 30000; simp _bit0_mul _bit1_mul.
lemma: 1000 * 30 = 30000; simp _bit0_mul_bit0 _bit0_mul_bit1 _bit1_mul_bit0 _bit1_mul_bit1.
