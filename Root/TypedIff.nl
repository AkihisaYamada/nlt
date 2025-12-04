import Base.

fix (:) prop (⟺).

assume imp_type! P : prop ⟹ Q : prop ⟹ (P ⟹ Q) : prop.
assume iff_type! P : prop ⟹ Q : prop ⟹ (P ⟺ Q) : prop.
assume iff_intro: (P ⟹ Q) ⟹ (Q ⟹ P) ⟹ P : prop ⟹ Q : prop ⟹ (P ⟺ Q).
assume iff_elim1: (P ⟺ Q) ⟹ P ⟹ P : prop ⟹ Q : prop ⟹ Q.
assume iff_elim2: (P ⟺ Q) ⟹ Q ⟹ P : prop ⟹ Q : prop ⟹ P.

begin

interpret iff: Magma prop (⟺).

interpret iff: Reflexive prop (⟺);
	by iff_intro.

note ! iff.refl.

interpret iff: Symmetric prop (⟺);
	for P Q if PQ: P ⟺ Q, !P : prop, !Q : prop then Q ⟺ P;
		apply iff_intro;
		- by iff_elim2[OF PQ].
		- by iff_elim1[OF PQ].
		.
	.

interpret iff: Transitive prop (⟺);
	for P Q R if PQ: P ⟺ Q, QR: Q ⟺ R, !P : prop, !Q : prop, !R : prop then P ⟺ R;
		apply iff_intro;
		- by iff_elim1[OF QR] iff_elim1[OF PQ].
		by iff_elim2[OF PQ] iff_elim2[OF QR].
	.

lemma iff_imp: if PQ: P ⟺ Q, [P : prop, Q : prop] then P ⟹ Q;
	by iff_elim1[OF PQ].

lemma iff_imp_rev: if PQ: P ⟺ Q, [P : prop, Q : prop] then Q ⟹ P;
	by iff_elim2[OF PQ].

set rewrite iff_imp iff_imp_rev iff.refl iff.trans.
set dual iff.sym.

lemma iff_cong_imp: for P Q
	if PP': P ⟺ P', QQ': P' ⟹ Q ⟺ Q', [P : prop, P' : prop, Q : prop, Q' : prop]
	then (P ⟹ Q) ⟺ (P' ⟹ Q');
	apply iff_intro;
	if PQ: P ⟹ Q;
		by PQ #fold QQ' PP'[dual].
	if P'Q': P' ⟹ Q', P: P;
		have P': P';
			by P[unfolded PP'].
		by P'Q'[OF P'] #unfold QQ'[OF P'].
	.

lemma iff_cong_imp_weak#cong: for P Q
	if PP': P ⟺ P', QQ': Q ⟺ Q', [P : prop, Q : prop, P' : prop, Q' : prop]
	then (P ⟹ Q) ⟺ (P' ⟹ Q');
	apply iff_intro;
	if PQ: P ⟹ Q;
		by PQ #fold QQ' PP'[dual].
	if P'Q': P' ⟹ Q';
		by P'Q' #unfold QQ' PP'[dual].
	.

lemma iff_cong_iff#cong: for P Q
	if PP': P ⟺ P', QQ': Q ⟺ Q', [P : prop, Q : prop, P' : prop, Q' : prop]
	then (P ⟺ Q) ⟺ (P' ⟺ Q');
	apply iff_intro;
	if PQ: P ⟺ Q;
		apply iff_intro;
		- by #unfold QQ'[dual] PQ[dual] PP'.
		- by #unfold PP'[dual] PQ QQ'.
		.
	if P'Q': P' ⟺ Q';
		apply iff_intro;
		- by #unfold QQ' P'Q'[dual] PP'[dual].
		- by #unfold PP' P'Q' QQ'[dual].
		.
	.

lemma imp_imp_iff: if [P, P : prop, Q : prop] then (P ⟹ Q) ⟺ Q;
	by iff_intro.

lemma imp_iff_iff: if [P, P : prop, Q : prop] then (P ⟺ Q) ⟺ Q;
	by iff_intro #elim iff_elim1.

lemma imp3_iff: if [P : prop, Q : prop] then (((P ⟹ Q) ⟹ Q) ⟹ Q) ⟺ (P ⟹ Q);
	apply iff_intro[OF imp2_imp_imp];
	if PQ: P ⟹ Q, PQQ: (P ⟹ Q) ⟹ Q then Q;
		by PQQ[OF PQ].
	.
end

