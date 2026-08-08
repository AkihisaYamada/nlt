
---
# Type-Free Intuitionistic Logic
---

import Iff, IntuitionisticNot, And, Or, Ex.

begin

instance Ex.Or.
instance And.

extend Eq begin

	instance Ex.
	instance And.

end
