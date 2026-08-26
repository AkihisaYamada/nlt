---
# Syntactic Safe Combinator
---
import Std.Syntactic.

begin

instance Id;
	by id_intro[for z, of (x. x = z)].

instance Const;
	by const_intro[for z, of (x. x = z)].

instance Comp;
	by o_intro[for z, of (x. x = z)].

instance Dual;
	by dual_intro[for z, of (x. x = z)].

instance BindComb;
	- by _BindAppBind_intro[for z, of (x. x = z)].
	- by _BindConst_intro[for z, of (x. x = z)].
	.

---
## Helper Combinators
---

definition app = (id ∘).

lemma app#simp app f x = f x; by #simp app_def.

-- Reverse application yields Church encoding of pairs.

definition[as revapp] (|>) = dual id.

lemma revapp#simp x |> f = f x; by #simp revapp_def.

lemma : ((z |>) ∘ (y |>) ∘ (x |>)) f = f x y z.

definition paracomp = dual ((∘) ∘ dual (∘)).

lemma paracomp_app#simp paracomp f g x y = f x (g y); by #simp paracomp_def.


definition _BindApp = (dual ((∘) ∘ _BindAppBind) _BindConst).

lemma _BindApp#simp _BindApp (x. F.[x]) s = (x. F.[x] s); by #simp _BindApp_def.

definition _AppBind = _BindAppBind ∘ _BindConst.

lemma _AppBind#simp _AppBind f (x. F.[x]) = (x. f F.[x]); by #simp _AppBind_def.

definition _BinderApp = dual ((∘) ∘ (∘)) _BindApp.

lemma _BinderApp#simp _BinderApp op (x. F.[x]) s = op (x. F.[x] s);
	by #simp _BinderApp_def.

definition _BindApp2 = ( _BindApp ∘) ∘ _BindAppBind.

lemma _BindApp2#simp _BindApp2 (x. F.[x]) (x. G.[x]) s = (x. F.[x] G.[x] s);
	by #simp _BindApp2_def.

definition _BindAppLeft = dual ∘ (( _BindAppBind ∘) ∘ _BindApp).

lemma _BindAppLeft#simp _BindAppLeft (x. F.[x]) (x. G.[x]) s = (x. F.[x] s G.[x]);
	by #simp _BindAppLeft_def.

definition _BindAppRight = dual ((∘) ∘ ((∘) ∘ _BindAppBind)) _BindApp.

lemma _BindAppRight#simp _BindAppRight (x. F.[x]) (x. G.[x]) s = (x. F.[x] (G.[x] s));
	by #simp _BindAppRight_def.

---
## Instantiating Pairs

We can already encode pairs by combinators, but letting pairs behave as functions can be confusing.
So we abstract the encoding by obtaining the pair constructor and destructor just with the specifications
`dest f (cons x y) = f x y`.
Since NLT kernel does not support simultaneous specification of multiple constants, we actually use
a combinator encoding to represent the tuple `(cons,dest)`.
---
obtain pair_tp where pair_tp_spec:
	if cons = pair_tp (const id), dest = pair_tp const
	then dest f (cons x y) = f x y;
	- for thesis if assm;
		apply assm[of ((dual ((∘) ∘ dual ∘ dual id) id |>) ∘ ((|>) |>))];
		- for cons if #simp for dest if #simp.
		.
	.

definition[as pair] (,) = pair_tp (const id).

definition pair_dest = pair_tp const.

lemma pair_dest#simp pair_dest f (x,y) = f x y;
	by pair_tp_spec[OF pair_def pair_dest_def].

definition pair_case = dual pair_dest.

lemma pair_case#simp pair_case (x,y) f = f x y;
	simp pair_case_def.

definition fst = pair_dest const.
definition snd = pair_dest (const id).

instance Pair; by #simp fst_def snd_def.

lemma pair_simp#elim
	if eq: simp ((x,y) = (x',y')), assm: simp (x = x') ⟹ simp (y = y') ⟹ P then P;
	apply pair_eq_pair_elim[OF eq[THEN simp_elim]]; by assm.

definition uncurry = dual ((∘) ∘ (∘)) (,).

lemma uncurry#simp uncurry f x y = f (x,y);
	simp uncurry_def.

definition pair_assoc = dual ((∘) ∘ (∘) ∘ (,)) (,).

lemma pair_assoc#simp pair_assoc x y z = (x,y,z);
	simp pair_assoc_def.

