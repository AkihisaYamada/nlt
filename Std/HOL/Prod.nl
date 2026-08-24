---
# Syntactic Products

As discussed in Typedef, syntactic products are necessary for formalizing the type definition mechanism.
Therefore, it seems simpler to assume that products of types are types, rather than defining them via type definition.
---
import type.Prod.
assume prod_type: if 'a : TYPE, 'b : TYPE then 'a × 'b : TYPE.

begin
