From PlutusCert Require Import
  (*  Util.List
     Util.DecOpt *)
  Language.PlutusIR
  Language.PlutusIR.Analysis.Equality.

Import NamedTerm.

From QuickChick Require Import QuickChick.



Instance Dec_eq_Strictness : Dec_Eq Strictness.
Proof. constructor. apply Strictness_dec. Defined.

Instance Dec_eq_Recursivity : Dec_Eq Recursivity.
Proof. constructor. apply Recursivity_dec. Defined.

Instance Dec_eq_DefaultFun : Dec_Eq DefaultFun.
Proof. constructor. apply func_dec. Defined.

Instance Dec_eq_DefaultUni : Dec_Eq DefaultUni.
Proof. constructor. apply DefaultUni_dec. Defined.

Instance Dec_eq_uniType {t} : Dec_Eq (uniType t).
Proof. constructor. apply uniType_dec. Defined.

Instance Dec_eq_valueOf {t} : Dec_Eq (valueOf t).
Proof. constructor. apply valueOf_dec. Defined.

Instance Dec_eq_typeIn {t} : Dec_Eq (typeIn t).
Proof. constructor. apply typeIn_dec. Defined.



Instance Dec_eq_some_valueOf : Dec_Eq (@some valueOf).
Proof. constructor. apply some_valueOf_dec. Defined.

Instance Dec_eq_some_typeIn: Dec_Eq (@some typeIn).
Proof. constructor. apply some_typeIn_dec. Defined.



Instance Dec_eq_Kind: Dec_Eq Kind.
Proof. constructor. apply Kind_dec. Defined.

Instance Dec_eq_Ty: Dec_Eq Ty.
Proof. constructor. apply Ty_dec. Defined.

Instance Dec_eq_VDecl: Dec_Eq VDecl.
Proof. constructor. apply VDecl_dec. Defined.

Instance Dec_eq_TVDecl: Dec_Eq TVDecl.
Proof. constructor. apply TVDecl_dec. Defined.

Instance Dec_eq_constructor: Dec_Eq constructor.
Proof. constructor. apply constructor_dec. Defined.

Instance Dec_eq_DTDecl: Dec_Eq DTDecl.
Proof. constructor. apply DTDecl_dec. Defined.

Instance Dec_eq_Term : Dec_Eq Term.
Proof. constructor. apply Term_dec. Defined.

Instance Dec_eq_Binding : Dec_Eq Binding.
Proof. constructor. apply binding_dec. Defined.
