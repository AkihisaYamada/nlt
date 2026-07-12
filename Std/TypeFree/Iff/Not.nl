import TypeFree.Not.

begin

extend ContraPos begin

	lemma not_cong#cong if PQ: P ⟺ Q then ¬ P ⟺ ¬ Q;
		apply+ iff_intro not.cmono;
		

	lemma 

end

