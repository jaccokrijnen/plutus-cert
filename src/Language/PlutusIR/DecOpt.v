From PlutusCert Require Import
  Language.PlutusIR.

Import NamedTerm.

From QuickChick Require Import QuickChick.

QCDerive EnumSized for DefaultUni.
QCDerive EnumSized for Strictness.

(* FIXME: Mock instance, here temporary. If not removed, might cause QuickChick to derive computation
    that does not actually function properly *)
Instance EnumSizedstring : EnumSized string :=
  {| enumSized _ := ret EmptyString |}.

Instance EnumSizedTy : EnumSized Ty :=
  {| enumSized _ := ret (Ty_Var EmptyString) |}.

Instance EnumSizedTerm : EnumSized Term :=
  {| enumSized _ := ret (Var EmptyString) |}.
