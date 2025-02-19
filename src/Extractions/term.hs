{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Main where

import qualified Prelude


#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#if __GLASGOW_HASKELL__ >= 900
import qualified GHC.Exts
#endif
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
#if __GLASGOW_HASKELL__ >= 900
unsafeCoerce = GHC.Exts.unsafeCoerce#
#else
unsafeCoerce = GHC.Base.unsafeCoerce#
#endif
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Base.Any
#else
-- HUGS
type Any = ()
#endif

data Unit =
   Tt

data Bool =
   True
 | False

data Nat =
   O
 | S Nat

data List a =
   Nil
 | Cons a (List a)

data Uint =
   Nil0
 | D0 Uint
 | D1 Uint
 | D2 Uint
 | D3 Uint
 | D4 Uint
 | D5 Uint
 | D6 Uint
 | D7 Uint
 | D8 Uint
 | D9 Uint

data Signed_int =
   Pos Uint
 | Neg Uint

revapp :: Uint -> Uint -> Uint
revapp d d' =
  case d of {
   Nil0 -> d';
   D0 d0 -> revapp d0 (D0 d');
   D1 d0 -> revapp d0 (D1 d');
   D2 d0 -> revapp d0 (D2 d');
   D3 d0 -> revapp d0 (D3 d');
   D4 d0 -> revapp d0 (D4 d');
   D5 d0 -> revapp d0 (D5 d');
   D6 d0 -> revapp d0 (D6 d');
   D7 d0 -> revapp d0 (D7 d');
   D8 d0 -> revapp d0 (D8 d');
   D9 d0 -> revapp d0 (D9 d')}

rev :: Uint -> Uint
rev d =
  revapp d Nil0

double :: Uint -> Uint
double d =
  case d of {
   Nil0 -> Nil0;
   D0 d0 -> D0 (double d0);
   D1 d0 -> D2 (double d0);
   D2 d0 -> D4 (double d0);
   D3 d0 -> D6 (double d0);
   D4 d0 -> D8 (double d0);
   D5 d0 -> D0 (succ_double d0);
   D6 d0 -> D2 (succ_double d0);
   D7 d0 -> D4 (succ_double d0);
   D8 d0 -> D6 (succ_double d0);
   D9 d0 -> D8 (succ_double d0)}

succ_double :: Uint -> Uint
succ_double d =
  case d of {
   Nil0 -> D1 Nil0;
   D0 d0 -> D1 (double d0);
   D1 d0 -> D3 (double d0);
   D2 d0 -> D5 (double d0);
   D3 d0 -> D7 (double d0);
   D4 d0 -> D9 (double d0);
   D5 d0 -> D1 (succ_double d0);
   D6 d0 -> D3 (succ_double d0);
   D7 d0 -> D5 (succ_double d0);
   D8 d0 -> D7 (succ_double d0);
   D9 d0 -> D9 (succ_double d0)}

data Byte =
   X00
 | X01
 | X02
 | X03
 | X04
 | X05
 | X06
 | X07
 | X08
 | X09
 | X0a
 | X0b
 | X0c
 | X0d
 | X0e
 | X0f
 | X10
 | X11
 | X12
 | X13
 | X14
 | X15
 | X16
 | X17
 | X18
 | X19
 | X1a
 | X1b
 | X1c
 | X1d
 | X1e
 | X1f
 | X20
 | X21
 | X22
 | X23
 | X24
 | X25
 | X26
 | X27
 | X28
 | X29
 | X2a
 | X2b
 | X2c
 | X2d
 | X2e
 | X2f
 | X30
 | X31
 | X32
 | X33
 | X34
 | X35
 | X36
 | X37
 | X38
 | X39
 | X3a
 | X3b
 | X3c
 | X3d
 | X3e
 | X3f
 | X40
 | X41
 | X42
 | X43
 | X44
 | X45
 | X46
 | X47
 | X48
 | X49
 | X4a
 | X4b
 | X4c
 | X4d
 | X4e
 | X4f
 | X50
 | X51
 | X52
 | X53
 | X54
 | X55
 | X56
 | X57
 | X58
 | X59
 | X5a
 | X5b
 | X5c
 | X5d
 | X5e
 | X5f
 | X60
 | X61
 | X62
 | X63
 | X64
 | X65
 | X66
 | X67
 | X68
 | X69
 | X6a
 | X6b
 | X6c
 | X6d
 | X6e
 | X6f
 | X70
 | X71
 | X72
 | X73
 | X74
 | X75
 | X76
 | X77
 | X78
 | X79
 | X7a
 | X7b
 | X7c
 | X7d
 | X7e
 | X7f
 | X80
 | X81
 | X82
 | X83
 | X84
 | X85
 | X86
 | X87
 | X88
 | X89
 | X8a
 | X8b
 | X8c
 | X8d
 | X8e
 | X8f
 | X90
 | X91
 | X92
 | X93
 | X94
 | X95
 | X96
 | X97
 | X98
 | X99
 | X9a
 | X9b
 | X9c
 | X9d
 | X9e
 | X9f
 | Xa0
 | Xa1
 | Xa2
 | Xa3
 | Xa4
 | Xa5
 | Xa6
 | Xa7
 | Xa8
 | Xa9
 | Xaa
 | Xab
 | Xac
 | Xad
 | Xae
 | Xaf
 | Xb0
 | Xb1
 | Xb2
 | Xb3
 | Xb4
 | Xb5
 | Xb6
 | Xb7
 | Xb8
 | Xb9
 | Xba
 | Xbb
 | Xbc
 | Xbd
 | Xbe
 | Xbf
 | Xc0
 | Xc1
 | Xc2
 | Xc3
 | Xc4
 | Xc5
 | Xc6
 | Xc7
 | Xc8
 | Xc9
 | Xca
 | Xcb
 | Xcc
 | Xcd
 | Xce
 | Xcf
 | Xd0
 | Xd1
 | Xd2
 | Xd3
 | Xd4
 | Xd5
 | Xd6
 | Xd7
 | Xd8
 | Xd9
 | Xda
 | Xdb
 | Xdc
 | Xdd
 | Xde
 | Xdf
 | Xe0
 | Xe1
 | Xe2
 | Xe3
 | Xe4
 | Xe5
 | Xe6
 | Xe7
 | Xe8
 | Xe9
 | Xea
 | Xeb
 | Xec
 | Xed
 | Xee
 | Xef
 | Xf0
 | Xf1
 | Xf2
 | Xf3
 | Xf4
 | Xf5
 | Xf6
 | Xf7
 | Xf8
 | Xf9
 | Xfa
 | Xfb
 | Xfc
 | Xfd
 | Xfe
 | Xff

data Positive =
   XI Positive
 | XO Positive
 | XH

data Z =
   Z0
 | Zpos Positive
 | Zneg Positive

to_little_uint :: Positive -> Uint
to_little_uint p =
  case p of {
   XI p0 -> succ_double (to_little_uint p0);
   XO p0 -> double (to_little_uint p0);
   XH -> D1 Nil0}

to_uint :: Positive -> Uint
to_uint p =
  rev (to_little_uint p)

to_int :: Z -> Signed_int
to_int n =
  case n of {
   Z0 -> Pos (D0 Nil0);
   Zpos p -> Pos (to_uint p);
   Zneg p -> Neg (to_uint p)}

data Ascii0 =
   Ascii Bool Bool Bool Bool Bool Bool Bool Bool

data String =
   EmptyString
 | String0 Ascii0 String

show_uint :: Uint -> String
show_uint n =
  case n of {
   Nil0 -> EmptyString;
   D0 n0 -> String0 (Ascii False False False False True True False False)
    (show_uint n0);
   D1 n0 -> String0 (Ascii True False False False True True False False)
    (show_uint n0);
   D2 n0 -> String0 (Ascii False True False False True True False False)
    (show_uint n0);
   D3 n0 -> String0 (Ascii True True False False True True False False)
    (show_uint n0);
   D4 n0 -> String0 (Ascii False False True False True True False False)
    (show_uint n0);
   D5 n0 -> String0 (Ascii True False True False True True False False)
    (show_uint n0);
   D6 n0 -> String0 (Ascii False True True False True True False False)
    (show_uint n0);
   D7 n0 -> String0 (Ascii True True True False True True False False)
    (show_uint n0);
   D8 n0 -> String0 (Ascii False False False True True True False False)
    (show_uint n0);
   D9 n0 -> String0 (Ascii True False False True True True False False)
    (show_uint n0)}

show_int :: Signed_int -> String
show_int n =
  case n of {
   Pos n0 -> show_uint n0;
   Neg n0 -> String0 (Ascii True False True True False True False False)
    (show_uint n0)}

show_Z :: Z -> String
show_Z n =
  show_int (to_int n)

data Recursivity =
   NonRec
 | Rec

data Strictness =
   NonStrict
 | Strict

data DefaultUni =
   DefaultUniInteger
 | DefaultUniByteString
 | DefaultUniString
 | DefaultUniUnit
 | DefaultUniBool
 | DefaultUniProtoList
 | DefaultUniProtoPair
 | DefaultUniData
 | DefaultUniBLS12_381_G1_Element
 | DefaultUniBLS12_381_G2_Element
 | DefaultUniBLS12_381_MlResult
 | DefaultUniApply DefaultUni DefaultUni

type UniType = Any

data Constant =
   ValueOf DefaultUni UniType

data DefaultFun =
   AddInteger
 | SubtractInteger
 | MultiplyInteger
 | DivideInteger
 | QuotientInteger
 | RemainderInteger
 | ModInteger
 | EqualsInteger
 | LessThanInteger
 | LessThanEqualsInteger
 | AppendByteString
 | ConsByteString
 | SliceByteString
 | LengthOfByteString
 | IndexByteString
 | EqualsByteString
 | LessThanByteString
 | LessThanEqualsByteString
 | Sha2_256
 | Sha3_256
 | Blake2b_256
 | VerifyEd25519Signature
 | VerifyEcdsaSecp256k1Signature
 | VerifySchnorrSecp256k1Signature
 | AppendString
 | EqualsString
 | EncodeUtf8
 | DecodeUtf8
 | IfThenElse
 | ChooseUnit
 | Trace
 | FstPair
 | SndPair
 | ChooseList
 | MkCons
 | HeadList
 | TailList
 | NullList
 | ChooseData
 | ConstrData
 | MapData
 | ListData
 | IData
 | BData
 | UnConstrData
 | UnMapData
 | UnListData
 | UnIData
 | UnBData
 | EqualsData
 | SerialiseData
 | MkPairData
 | MkNilData
 | MkNilPairData
 | Bls12_381_G1_add
 | Bls12_381_G1_neg
 | Bls12_381_G1_scalarMul
 | Bls12_381_G1_equal
 | Bls12_381_G1_hashToGroup
 | Bls12_381_G1_compress
 | Bls12_381_G1_uncompress
 | Bls12_381_G2_add
 | Bls12_381_G2_neg
 | Bls12_381_G2_scalarMul
 | Bls12_381_G2_equal
 | Bls12_381_G2_hashToGroup
 | Bls12_381_G2_compress
 | Bls12_381_G2_uncompress
 | Bls12_381_millerLoop
 | Bls12_381_mulMlResult
 | Bls12_381_finalVerify
 | Keccak_256
 | Blake2b_224
 | IntegerToByteString
 | ByteStringToInteger

type Name = String

type Tyname = String

type BinderName = String

type BinderTyname = String

data Kind =
   Kind_Base
 | Kind_Arrow Kind Kind

data Ty =
   Ty_Var Tyname
 | Ty_Fun Ty Ty
 | Ty_IFix Ty Ty
 | Ty_Forall BinderTyname Kind Ty
 | Ty_Builtin DefaultUni
 | Ty_Lam BinderTyname Kind Ty
 | Ty_App Ty Ty

data Vdecl =
   VarDecl BinderName Ty

data Tvdecl =
   TyVarDecl BinderTyname Kind

data Dtdecl =
   Datatype Tvdecl (List Tvdecl) BinderName (List Vdecl)

data Term =
   Let Recursivity (List Binding) Term
 | Var Name
 | TyAbs BinderTyname Kind Term
 | LamAbs BinderName Ty Term
 | Apply Term Term
 | Constant0 Constant
 | Builtin DefaultFun
 | TyInst Term Ty
 | Error Ty
 | IWrap Ty Ty Term
 | Unwrap Term
 | Constr Ty Nat (List Term)
 | Case Ty Term (List Term)
data Binding =
   TermBind Strictness Vdecl Term
 | TypeBind Tvdecl Ty
 | DatatypeBind Dtdecl

some :: a1 -> a1
some x =
  x

xorByteString :: DefaultFun
xorByteString =
  AddInteger

writeBits :: DefaultFun
writeBits =
  AddInteger

shiftByteString :: DefaultFun
shiftByteString =
  AddInteger

rotateByteString :: DefaultFun
rotateByteString =
  AddInteger

ripemd_160 :: DefaultFun
ripemd_160 =
  AddInteger

replicateByte :: DefaultFun
replicateByte =
  AddInteger

readBit :: DefaultFun
readBit =
  AddInteger

orByteString :: DefaultFun
orByteString =
  AddInteger

findFirstSetBit :: DefaultFun
findFirstSetBit =
  AddInteger

expModInteger :: DefaultFun
expModInteger =
  AddInteger

countSetBits :: DefaultFun
countSetBits =
  AddInteger

complementByteString :: DefaultFun
complementByteString =
  AddInteger

andByteString :: DefaultFun
andByteString =
  AddInteger

ast :: Term
ast =
  Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XO (XO (XI (XI (XI XH)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniBool) (Ty_Fun (Ty_Builtin DefaultUniByteString) (Ty_Fun
    (Ty_Builtin DefaultUniByteString) (Ty_Builtin DefaultUniByteString)))))
    (Builtin xorByteString)) Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XI (XO (XI (XI (XI XH)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Fun (Ty_App (Ty_Builtin DefaultUniProtoList)
    (Ty_Builtin DefaultUniInteger)) (Ty_Fun (Ty_Builtin DefaultUniBool)
    (Ty_Builtin DefaultUniByteString))))) (Builtin writeBits)) Nil) (Let
    NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XI (XI (XI (XO XH))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Fun (Ty_Builtin DefaultUniByteString) (Ty_Fun
    (Ty_Builtin DefaultUniByteString) (Ty_Builtin DefaultUniBool)))))
    (Builtin VerifySchnorrSecp256k1Signature)) Nil) (Let NonRec (Cons
    (TermBind Strict (VarDecl (show_Z (Zpos (XI (XO (XI (XI (XO XH)))))))
    (Ty_Fun (Ty_Builtin DefaultUniByteString) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Fun (Ty_Builtin DefaultUniByteString)
    (Ty_Builtin DefaultUniBool))))) (Builtin VerifyEd25519Signature)) Nil)
    (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XI (XI (XI (XO XH))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Fun (Ty_Builtin DefaultUniByteString) (Ty_Fun
    (Ty_Builtin DefaultUniByteString) (Ty_Builtin DefaultUniBool)))))
    (Builtin VerifyEcdsaSecp256k1Signature)) Nil) (Let NonRec (Cons (TermBind
    Strict (VarDecl (show_Z (Zpos (XO (XO (XO (XI (XI (XO XH)))))))) (Ty_Fun
    (Ty_Builtin DefaultUniData) (Ty_App (Ty_Builtin DefaultUniProtoList)
    (Ty_App (Ty_App (Ty_Builtin DefaultUniProtoPair) (Ty_Builtin
    DefaultUniData)) (Ty_Builtin DefaultUniData))))) (Builtin UnMapData))
    Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XO (XO (XI (XI (XO XH)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniData) (Ty_App (Ty_Builtin DefaultUniProtoList) (Ty_Builtin
    DefaultUniData)))) (Builtin UnListData)) Nil) (Let NonRec (Cons (TermBind
    Strict (VarDecl (show_Z (Zpos (XO (XI (XO (XI (XI (XO XH)))))))) (Ty_Fun
    (Ty_Builtin DefaultUniData) (Ty_Builtin DefaultUniInteger))) (Builtin
    UnIData)) Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XI (XI (XO (XI (XO XH)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniData) (Ty_App (Ty_App (Ty_Builtin DefaultUniProtoPair)
    (Ty_Builtin DefaultUniInteger)) (Ty_App (Ty_Builtin DefaultUniProtoList)
    (Ty_Builtin DefaultUniData))))) (Builtin UnConstrData)) Nil) (Let NonRec
    (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XI (XO (XI (XI (XO XH)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniData) (Ty_Builtin DefaultUniByteString))) (Builtin UnBData))
    Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XI (XI XH))))) (Ty_Builtin DefaultUniUnit)) (Constant0
    (some (ValueOf DefaultUniUnit (unsafeCoerce Tt))))) Nil) (Let NonRec
    (Cons (TermBind Strict (VarDecl (show_Z (Zpos (XO (XO (XO (XO XH))))))
    (Ty_Builtin DefaultUniBool)) (Constant0
    (some (ValueOf DefaultUniBool (unsafeCoerce True))))) Nil) (Let NonRec
    (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XO (XO (XI (XI XH))))))) (Ty_Forall
    (show_Z (Zpos (XO (XO (XO (XI (XI XH))))))) Kind_Base (Ty_Fun (Ty_Builtin
    DefaultUniString) (Ty_Fun (Ty_Var
    (show_Z (Zpos (XO (XO (XO (XI (XI XH)))))))) (Ty_Var
    (show_Z (Zpos (XO (XO (XO (XI (XI XH)))))))))))) (Builtin Trace)) Nil)
    (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XI (XO (XI (XO (XO XH)))))))) (Ty_Forall
    (show_Z (Zpos (XO (XI (XO (XI (XO (XO XH)))))))) Kind_Base (Ty_Fun
    (Ty_App (Ty_Builtin DefaultUniProtoList) (Ty_Var
    (show_Z (Zpos (XO (XI (XO (XI (XO (XO XH)))))))))) (Ty_App (Ty_Builtin
    DefaultUniProtoList) (Ty_Var
    (show_Z (Zpos (XO (XI (XO (XI (XO (XO XH))))))))))))) (Builtin TailList))
    Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XO (XO (XI XH)))))) (Ty_Fun (Ty_Builtin
    DefaultUniInteger) (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Builtin
    DefaultUniInteger)))) (Builtin SubtractInteger)) Nil) (Let NonRec (Cons
    (TermBind Strict (VarDecl (show_Z (Zpos (XI (XI (XI (XI (XI XH)))))))
    (Ty_Forall (show_Z (Zpos (XI (XO (XI (XI (XI XH))))))) Kind_Base
    (Ty_Forall (show_Z (Zpos (XO (XI (XI (XI (XI XH))))))) Kind_Base (Ty_Fun
    (Ty_App (Ty_App (Ty_Builtin DefaultUniProtoPair) (Ty_Var
    (show_Z (Zpos (XI (XO (XI (XI (XI XH))))))))) (Ty_Var
    (show_Z (Zpos (XO (XI (XI (XI (XI XH))))))))) (Ty_Var
    (show_Z (Zpos (XO (XI (XI (XI (XI XH)))))))))))) (Builtin SndPair)) Nil)
    (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XO (XI (XO (XO XH))))))) (Ty_Fun (Ty_Builtin
    DefaultUniInteger) (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Fun
    (Ty_Builtin DefaultUniByteString) (Ty_Builtin DefaultUniByteString)))))
    (Builtin SliceByteString)) Nil) (Let NonRec (Cons (TermBind Strict
    (VarDecl (show_Z (Zpos (XI (XO (XI (XI (XI (XI XH)))))))) (Ty_Fun
    (Ty_Builtin DefaultUniByteString) (Ty_Fun (Ty_Builtin DefaultUniInteger)
    (Ty_Builtin DefaultUniByteString)))) (Builtin shiftByteString)) Nil) (Let
    NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XI (XO (XI (XO XH))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Builtin DefaultUniByteString))) (Builtin
    Sha3_256)) Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XI (XO (XI (XO XH))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Builtin DefaultUniByteString))) (Builtin
    Sha2_256)) Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XO (XI (XI (XI (XO XH)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniData) (Ty_Builtin DefaultUniByteString))) (Builtin
    SerialiseData)) Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XI (XI (XI (XI (XI XH)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Builtin
    DefaultUniByteString)))) (Builtin rotateByteString)) Nil) (Let NonRec
    (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XO (XO (XO (XO (XO (XO XH))))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Builtin DefaultUniByteString))) (Builtin
    ripemd_160)) Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XO (XI (XI (XI (XI XH)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniInteger) (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Builtin
    DefaultUniByteString)))) (Builtin replicateByte)) Nil) (Let NonRec (Cons
    (TermBind Strict (VarDecl (show_Z (Zpos (XI (XO (XI (XI XH)))))) (Ty_Fun
    (Ty_Builtin DefaultUniInteger) (Ty_Fun (Ty_Builtin DefaultUniInteger)
    (Ty_Builtin DefaultUniInteger)))) (Builtin RemainderInteger)) Nil) (Let
    NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XI (XO (XI (XI (XI XH)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Builtin
    DefaultUniBool)))) (Builtin readBit)) Nil) (Let NonRec (Cons (TermBind
    Strict (VarDecl (show_Z (Zpos (XO (XO (XI (XI XH)))))) (Ty_Fun
    (Ty_Builtin DefaultUniInteger) (Ty_Fun (Ty_Builtin DefaultUniInteger)
    (Ty_Builtin DefaultUniInteger)))) (Builtin QuotientInteger)) Nil) (Let
    NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XI (XI (XO (XI (XI XH)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniBool) (Ty_Fun (Ty_Builtin DefaultUniByteString) (Ty_Fun
    (Ty_Builtin DefaultUniByteString) (Ty_Builtin DefaultUniByteString)))))
    (Builtin orByteString)) Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XO (XI (XI (XO (XO XH)))))))) (Ty_Forall
    (show_Z (Zpos (XO (XO (XI (XI (XO (XO XH)))))))) Kind_Base (Ty_Fun
    (Ty_App (Ty_Builtin DefaultUniProtoList) (Ty_Var
    (show_Z (Zpos (XO (XO (XI (XI (XO (XO XH)))))))))) (Ty_Builtin
    DefaultUniBool)))) (Builtin NullList)) Nil) (Let NonRec (Cons (TermBind
    Strict (VarDecl (show_Z (Zpos (XO (XI (XO (XI XH)))))) (Ty_Fun
    (Ty_Builtin DefaultUniInteger) (Ty_Fun (Ty_Builtin DefaultUniInteger)
    (Ty_Builtin DefaultUniInteger)))) (Builtin MultiplyInteger)) Nil) (Let
    NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XI (XI (XI XH)))))) (Ty_Fun (Ty_Builtin
    DefaultUniInteger) (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Builtin
    DefaultUniInteger)))) (Builtin ModInteger)) Nil) (Let NonRec (Cons
    (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XI (XI (XI (XI (XO XH)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniData) (Ty_Fun (Ty_Builtin DefaultUniData) (Ty_App (Ty_App
    (Ty_Builtin DefaultUniProtoPair) (Ty_Builtin DefaultUniData)) (Ty_Builtin
    DefaultUniData))))) (Builtin MkPairData)) Nil) (Let NonRec (Cons
    (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XO (XO (XO (XO (XI XH)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniUnit) (Ty_App (Ty_Builtin DefaultUniProtoList) (Ty_App (Ty_App
    (Ty_Builtin DefaultUniProtoPair) (Ty_Builtin DefaultUniData)) (Ty_Builtin
    DefaultUniData))))) (Builtin MkNilPairData)) Nil) (Let NonRec (Cons
    (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XI (XI (XI (XI (XO XH)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniUnit) (Ty_App (Ty_Builtin DefaultUniProtoList) (Ty_Builtin
    DefaultUniData)))) (Builtin MkNilData)) Nil) (Let NonRec (Cons (TermBind
    Strict (VarDecl (show_Z (Zpos (XI (XI (XO (XO (XI (XO XH)))))))) (Ty_Fun
    (Ty_App (Ty_Builtin DefaultUniProtoList) (Ty_App (Ty_App (Ty_Builtin
    DefaultUniProtoPair) (Ty_Builtin DefaultUniData)) (Ty_Builtin
    DefaultUniData))) (Ty_Builtin DefaultUniData))) (Builtin MapData)) Nil)
    (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XO (XI (XO (XI (XO XH)))))))) (Ty_Fun (Ty_App
    (Ty_Builtin DefaultUniProtoList) (Ty_Builtin DefaultUniData)) (Ty_Builtin
    DefaultUniData))) (Builtin ListData)) Nil) (Let NonRec (Cons (TermBind
    Strict (VarDecl (show_Z (Zpos (XI (XO (XI (XO (XI (XO XH)))))))) (Ty_Fun
    (Ty_Builtin DefaultUniInteger) (Ty_Builtin DefaultUniData))) (Builtin
    IData)) Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XI (XO (XO (XI (XO XH)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniInteger) (Ty_Fun (Ty_App (Ty_Builtin DefaultUniProtoList)
    (Ty_Builtin DefaultUniData)) (Ty_Builtin DefaultUniData)))) (Builtin
    ConstrData)) Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XI (XI (XO (XO (XO XH)))))))) (Ty_Forall
    (show_Z (Zpos (XO (XI (XI (XO (XO (XO XH)))))))) Kind_Base (Ty_Fun
    (Ty_Var (show_Z (Zpos (XO (XI (XI (XO (XO (XO XH))))))))) (Ty_Fun (Ty_App
    (Ty_Builtin DefaultUniProtoList) (Ty_Var
    (show_Z (Zpos (XO (XI (XI (XO (XO (XO XH)))))))))) (Ty_App (Ty_Builtin
    DefaultUniProtoList) (Ty_Var
    (show_Z (Zpos (XO (XI (XI (XO (XO (XO XH)))))))))))))) (Builtin MkCons))
    Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XI (XI (XO (XI (XO XH)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Builtin DefaultUniData))) (Builtin BData)) Nil)
    (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XO (XO (XO (XO XH))))))) (Ty_Fun (Ty_Builtin
    DefaultUniInteger) (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Builtin
    DefaultUniBool)))) (Builtin LessThanInteger)) Nil) (Let NonRec (Cons
    (TermBind Strict (VarDecl (show_Z (Zpos (XI (XO (XO (XO (XO XH)))))))
    (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Fun (Ty_Builtin
    DefaultUniInteger) (Ty_Builtin DefaultUniBool)))) (Builtin
    LessThanEqualsInteger)) Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XO (XO (XI (XO XH))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Fun (Ty_Builtin DefaultUniByteString)
    (Ty_Builtin DefaultUniBool)))) (Builtin LessThanEqualsByteString)) Nil)
    (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XO (XO (XI (XO XH))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Fun (Ty_Builtin DefaultUniByteString)
    (Ty_Builtin DefaultUniBool)))) (Builtin LessThanByteString)) Nil) (Let
    NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XO (XI (XO (XO XH))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Builtin DefaultUniInteger))) (Builtin
    LengthOfByteString)) Nil) (Let NonRec (Cons (TermBind NonStrict (VarDecl
    (show_Z (Zpos (XI (XI (XI (XI (XO (XO (XO XH))))))))) (Ty_Forall
    (show_Z (Zpos (XO (XI (XI (XI (XO (XO (XO XH))))))))) Kind_Base (Ty_Fun
    (Ty_Var (show_Z (Zpos (XO (XI (XI (XI (XO (XO (XO XH)))))))))) (Ty_Var
    (show_Z (Zpos (XO (XI (XI (XI (XO (XO (XO XH))))))))))))) (TyAbs
    (show_Z (Zpos (XO (XO (XO (XO (XI (XO (XO XH))))))))) Kind_Base (LamAbs
    (show_Z (Zpos (XI (XO (XO (XO (XI (XO (XO XH))))))))) (Ty_Var
    (show_Z (Zpos (XO (XO (XO (XO (XI (XO (XO XH)))))))))) (Var
    (show_Z (Zpos (XI (XO (XO (XO (XI (XO (XO XH))))))))))))) Nil) (Let
    NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XO (XI (XO (XO (XO XH)))))))) (Ty_Forall
    (show_Z (Zpos (XI (XI (XO (XO (XO (XO XH)))))))) Kind_Base (Ty_Forall
    (show_Z (Zpos (XO (XO (XI (XO (XO (XO XH)))))))) Kind_Base (Ty_Fun
    (Ty_Var (show_Z (Zpos (XO (XO (XI (XO (XO (XO XH))))))))) (Ty_Fun (Ty_Fun
    (Ty_Var (show_Z (Zpos (XI (XI (XO (XO (XO (XO XH))))))))) (Ty_Fun (Ty_App
    (Ty_Builtin DefaultUniProtoList) (Ty_Var
    (show_Z (Zpos (XI (XI (XO (XO (XO (XO XH)))))))))) (Ty_Var
    (show_Z (Zpos (XO (XO (XI (XO (XO (XO XH))))))))))) (Ty_Fun (Ty_App
    (Ty_Builtin DefaultUniProtoList) (Ty_Var
    (show_Z (Zpos (XI (XI (XO (XO (XO (XO XH)))))))))) (Ty_Var
    (show_Z (Zpos (XO (XO (XI (XO (XO (XO XH))))))))))))))) (TyAbs
    (show_Z Z0) Kind_Base (TyAbs (show_Z (Zpos XH)) Kind_Base (LamAbs
    (show_Z (Zpos (XO (XO XH)))) (Ty_Var (show_Z (Zpos XH))) (LamAbs
    (show_Z (Zpos (XI (XO XH)))) (Ty_Fun (Ty_Var (show_Z Z0)) (Ty_Fun (Ty_App
    (Ty_Builtin DefaultUniProtoList) (Ty_Var (show_Z Z0))) (Ty_Var
    (show_Z (Zpos XH))))) (LamAbs (show_Z (Zpos (XI XH))) (Ty_App (Ty_Builtin
    DefaultUniProtoList) (Ty_Var (show_Z Z0))) (TyInst (Apply (Apply (Apply
    (TyInst (TyInst (Builtin ChooseList) (Ty_Var (show_Z Z0))) (Ty_Forall
    (show_Z (Zpos (XO XH))) Kind_Base (Ty_Var (show_Z (Zpos XH))))) (Var
    (show_Z (Zpos (XI XH))))) (TyAbs (show_Z (Zpos (XO XH))) Kind_Base (Var
    (show_Z (Zpos (XO (XO XH))))))) (TyAbs (show_Z (Zpos (XO XH))) Kind_Base
    (Apply (Apply (Var (show_Z (Zpos (XI (XO XH))))) (Apply (TyInst (Builtin
    HeadList) (Ty_Var (show_Z Z0))) (Var (show_Z (Zpos (XI XH)))))) (Apply
    (TyInst (Builtin TailList) (Ty_Var (show_Z Z0))) (Var
    (show_Z (Zpos (XI XH)))))))) (Ty_Var (show_Z (Zpos XH)))))))))) Nil) (Let
    NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XO (XO (XI XH)))))) (Ty_Fun (Ty_Builtin
    DefaultUniInteger) (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Builtin
    DefaultUniInteger)))) (Builtin AddInteger)) Nil) (Let NonRec (Cons
    (TypeBind (TyVarDecl (show_Z (Zpos (XI (XI XH)))) (Kind_Arrow Kind_Base
    Kind_Base)) (Ty_Builtin DefaultUniProtoList)) Nil) (Let NonRec (Cons
    (TypeBind (TyVarDecl (show_Z (Zpos (XI (XO XH)))) Kind_Base) (Ty_Builtin
    DefaultUniData)) Nil) (Let NonRec (Cons (TypeBind (TyVarDecl
    (show_Z (Zpos (XO (XI (XI (XO (XO (XO (XO XH))))))))) (Kind_Arrow
    Kind_Base Kind_Base)) (Ty_Lam
    (show_Z (Zpos (XI (XI (XI (XO (XO (XO (XO XH))))))))) Kind_Base (Ty_App
    (Ty_Builtin DefaultUniProtoList) (Ty_Builtin DefaultUniData)))) Nil) (Let
    NonRec (Cons (TypeBind (TyVarDecl (show_Z (Zpos XH)) Kind_Base)
    (Ty_Builtin DefaultUniInteger)) Nil) (Let NonRec (Cons (TermBind
    NonStrict (VarDecl (show_Z (Zpos (XO (XO (XO (XI (XO (XO (XO XH)))))))))
    (Ty_Forall (show_Z (Zpos (XI (XO (XI (XO (XO (XO (XO XH)))))))))
    Kind_Base (Ty_Fun (Ty_App (Ty_Lam
    (show_Z (Zpos (XI (XI (XI (XO (XO (XO (XO XH))))))))) Kind_Base (Ty_App
    (Ty_Builtin DefaultUniProtoList) (Ty_Builtin DefaultUniData))) (Ty_Var
    (show_Z (Zpos (XI (XO (XI (XO (XO (XO (XO XH))))))))))) (Ty_Builtin
    DefaultUniInteger)))) (TyAbs
    (show_Z (Zpos (XI (XO (XO (XI (XO (XO (XO XH))))))))) Kind_Base (LamAbs
    (show_Z (Zpos (XO (XI (XO (XI (XO (XO (XO XH))))))))) (Ty_App (Ty_Lam
    (show_Z (Zpos (XI (XI (XI (XO (XO (XO (XO XH))))))))) Kind_Base (Ty_App
    (Ty_Builtin DefaultUniProtoList) (Ty_Builtin DefaultUniData))) (Ty_Var
    (show_Z (Zpos (XI (XO (XO (XI (XO (XO (XO XH))))))))))) (Let NonRec (Cons
    (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XI (XO (XI (XO (XO (XO XH))))))))) (Ty_App (Ty_Builtin
    DefaultUniProtoList) (Ty_Builtin DefaultUniData))) (Var
    (show_Z (Zpos (XO (XI (XO (XI (XO (XO (XO XH))))))))))) Nil) (Let NonRec
    (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XO (XI (XI (XI (XO (XO XH))))))))) (Ty_Forall
    (show_Z (Zpos (XO (XO (XI (XI (XI (XO (XO XH))))))))) Kind_Base (Ty_Fun
    (Ty_App (Ty_Builtin DefaultUniProtoList) (Ty_Var
    (show_Z (Zpos (XO (XO (XI (XI (XI (XO (XO XH))))))))))) (Ty_Fun
    (Ty_Builtin DefaultUniInteger) (Ty_Builtin DefaultUniInteger))))) (TyAbs
    (show_Z (Zpos (XO (XO (XI (XI (XO (XO (XO XH))))))))) Kind_Base (Let Rec
    (Cons (TermBind NonStrict (VarDecl
    (show_Z (Zpos (XI (XO (XI (XI (XO (XO (XO XH))))))))) (Ty_Fun (Ty_App
    (Ty_Builtin DefaultUniProtoList) (Ty_Var
    (show_Z (Zpos (XO (XO (XI (XI (XO (XO (XO XH))))))))))) (Ty_Fun
    (Ty_Builtin DefaultUniInteger) (Ty_Builtin DefaultUniInteger)))) (Apply
    (Apply (TyInst (TyInst (Var
    (show_Z (Zpos (XI (XO (XI (XO (XO (XO XH))))))))) (Ty_Var
    (show_Z (Zpos (XO (XO (XI (XI (XO (XO (XO XH))))))))))) (Ty_Fun
    (Ty_Builtin DefaultUniInteger) (Ty_Builtin DefaultUniInteger))) (TyInst
    (Var (show_Z (Zpos (XI (XI (XI (XI (XO (XO (XO XH)))))))))) (Ty_Builtin
    DefaultUniInteger))) (LamAbs
    (show_Z (Zpos (XO (XI (XO (XO (XI (XO (XO XH))))))))) (Ty_Var
    (show_Z (Zpos (XO (XO (XI (XI (XO (XO (XO XH)))))))))) (LamAbs
    (show_Z (Zpos (XI (XI (XO (XO (XI (XO (XO XH))))))))) (Ty_App (Ty_Builtin
    DefaultUniProtoList) (Ty_Var
    (show_Z (Zpos (XO (XO (XI (XI (XO (XO (XO XH))))))))))) (Let NonRec (Cons
    (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XO (XI (XO (XI (XO (XO XH))))))))) (Ty_Var
    (show_Z (Zpos (XO (XO (XI (XI (XO (XO (XO XH))))))))))) (Var
    (show_Z (Zpos (XO (XI (XO (XO (XI (XO (XO XH))))))))))) Nil) (Let NonRec
    (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XO (XI (XO (XI (XO (XO XH))))))))) (Ty_App (Ty_Builtin
    DefaultUniProtoList) (Ty_Var
    (show_Z (Zpos (XO (XO (XI (XI (XO (XO (XO XH)))))))))))) (Var
    (show_Z (Zpos (XI (XI (XO (XO (XI (XO (XO XH))))))))))) Nil) (Let NonRec
    (Cons (TermBind NonStrict (VarDecl
    (show_Z (Zpos (XO (XI (XI (XO (XI (XO (XO XH))))))))) (Ty_Builtin
    DefaultUniInteger)) (Constant0
    (some (ValueOf DefaultUniInteger (unsafeCoerce (Zpos XH)))))) Nil) (Let
    NonRec (Cons (TermBind NonStrict (VarDecl
    (show_Z (Zpos (XI (XI (XI (XO (XI (XO (XO XH))))))))) (Ty_Fun (Ty_Builtin
    DefaultUniInteger) (Ty_Builtin DefaultUniInteger))) (Apply (Var
    (show_Z (Zpos (XI (XO (XI (XI (XO (XO (XO XH)))))))))) (Var
    (show_Z (Zpos (XI (XO (XI (XO (XI (XO (XO XH)))))))))))) Nil) (LamAbs
    (show_Z (Zpos (XO (XO (XO (XI (XI (XO (XO XH))))))))) (Ty_Builtin
    DefaultUniInteger) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XO (XO (XI (XI (XO (XO XH))))))))) (Ty_Fun (Ty_Builtin
    DefaultUniInteger) (Ty_Builtin DefaultUniInteger))) (Var
    (show_Z (Zpos (XI (XI (XI (XO (XI (XO (XO XH))))))))))) Nil) (Let NonRec
    (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XI (XO (XI (XI (XO (XO XH))))))))) (Ty_Builtin
    DefaultUniInteger)) (Var
    (show_Z (Zpos (XO (XO (XO (XI (XI (XO (XO XH))))))))))) Nil) (Let NonRec
    (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XI (XO (XI (XI (XO (XO XH))))))))) (Ty_Builtin
    DefaultUniInteger)) (Apply (Var
    (show_Z (Zpos (XI (XO (XO (XI (XI (XO (XO XH)))))))))) (Var
    (show_Z (Zpos (XO (XI (XO (XI (XI (XO (XO XH)))))))))))) Nil) (Apply
    (Apply (Var (show_Z (Zpos (XO (XO (XO (XI XH))))))) (Var
    (show_Z (Zpos (XO (XI (XI (XO (XI (XO (XO XH))))))))))) (Var
    (show_Z (Zpos (XI (XI (XO (XI (XI (XO (XO XH))))))))))))))))))))))) Nil)
    (Var (show_Z (Zpos (XI (XO (XI (XI (XO (XO (XO XH))))))))))))) Nil)
    (Apply (Apply (TyInst (Var
    (show_Z (Zpos (XI (XO (XI (XI (XI (XO (XO XH)))))))))) (Ty_Builtin
    DefaultUniData)) (Var
    (show_Z (Zpos (XI (XI (XO (XI (XO (XO (XO XH))))))))))) (Constant0
    (some (ValueOf DefaultUniInteger (unsafeCoerce Z0)))))))))) Nil) (Let
    NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XI (XO (XO (XI (XI XH)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Builtin DefaultUniByteString))) (Builtin
    Keccak_256)) Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XO (XI (XO (XI (XI XH)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniBool) (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Fun
    (Ty_Builtin DefaultUniInteger) (Ty_Builtin DefaultUniByteString)))))
    (Builtin IntegerToByteString)) Nil) (Let NonRec (Cons (TermBind Strict
    (VarDecl (show_Z (Zpos (XI (XI (XO (XO (XO (XO (XO XH))))))))) (Ty_Fun
    (Ty_Builtin DefaultUniInteger) (Ty_Builtin DefaultUniInteger))) (LamAbs
    (show_Z (Zpos (XO (XO (XI (XO (XO (XO (XO XH))))))))) (Ty_Builtin
    DefaultUniInteger) (Apply (Apply (Builtin SubtractInteger) (Constant0
    (some (ValueOf DefaultUniInteger (unsafeCoerce Z0))))) (Var
    (show_Z (Zpos (XO (XO (XI (XO (XO (XO (XO XH))))))))))))) Nil) (Let
    NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XI (XI (XO (XO XH))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Builtin
    DefaultUniInteger)))) (Builtin IndexByteString)) Nil) (Let NonRec (Cons
    (TermBind Strict (VarDecl (show_Z (Zpos (XI (XO (XI (XO (XI XH)))))))
    (Ty_Forall (show_Z (Zpos (XO (XO (XI (XO (XI XH))))))) Kind_Base (Ty_Fun
    (Ty_Builtin DefaultUniBool) (Ty_Fun (Ty_Var
    (show_Z (Zpos (XO (XO (XI (XO (XI XH)))))))) (Ty_Fun (Ty_Var
    (show_Z (Zpos (XO (XO (XI (XO (XI XH)))))))) (Ty_Var
    (show_Z (Zpos (XO (XO (XI (XO (XI XH))))))))))))) (Builtin IfThenElse))
    Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XO (XO (XI (XO (XO XH)))))))) (Ty_Forall
    (show_Z (Zpos (XO (XO (XO (XI (XO (XO XH)))))))) Kind_Base (Ty_Fun
    (Ty_App (Ty_Builtin DefaultUniProtoList) (Ty_Var
    (show_Z (Zpos (XO (XO (XO (XI (XO (XO XH)))))))))) (Ty_Var
    (show_Z (Zpos (XO (XO (XO (XI (XO (XO XH)))))))))))) (Builtin HeadList))
    Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XO (XI (XI (XI XH))))))) (Ty_Forall
    (show_Z (Zpos (XO (XI (XO (XI (XI XH))))))) Kind_Base (Ty_Forall
    (show_Z (Zpos (XI (XI (XO (XI (XI XH))))))) Kind_Base (Ty_Fun (Ty_App
    (Ty_App (Ty_Builtin DefaultUniProtoPair) (Ty_Var
    (show_Z (Zpos (XO (XI (XO (XI (XI XH))))))))) (Ty_Var
    (show_Z (Zpos (XI (XI (XO (XI (XI XH))))))))) (Ty_Var
    (show_Z (Zpos (XO (XI (XO (XI (XI XH)))))))))))) (Builtin FstPair)) Nil)
    (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XO (XO (XO (XO (XO (XO XH))))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Builtin DefaultUniInteger))) (Builtin
    findFirstSetBit)) Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XO (XO (XO XH)))))) (Ty_Builtin DefaultUniBool))
    (Constant0 (some (ValueOf DefaultUniBool (unsafeCoerce False))))) Nil)
    (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XI (XO (XO (XO (XO (XO XH))))))))) (Ty_Fun (Ty_Builtin
    DefaultUniInteger) (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Fun
    (Ty_Builtin DefaultUniInteger) (Ty_Builtin DefaultUniInteger)))))
    (Builtin expModInteger)) Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XI (XI XH))))) (Ty_Forall
    (show_Z (Zpos (XI (XO (XI XH))))) Kind_Base (Ty_Fun (Ty_Builtin
    DefaultUniUnit) (Ty_Var (show_Z (Zpos (XI (XO (XI XH))))))))) (TyAbs
    (show_Z (Zpos (XI (XI (XO XH))))) Kind_Base (LamAbs
    (show_Z (Zpos (XO (XO (XI XH))))) (Ty_Builtin DefaultUniUnit) (Error
    (Ty_Var (show_Z (Zpos (XI (XI (XO XH)))))))))) Nil) (Let NonRec (Cons
    (TermBind Strict (VarDecl (show_Z (Zpos (XI (XO (XO (XO (XI XH)))))))
    (Ty_Fun (Ty_Builtin DefaultUniString) (Ty_Fun (Ty_Builtin
    DefaultUniString) (Ty_Builtin DefaultUniBool)))) (Builtin EqualsString))
    Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XI (XI (XI XH)))))) (Ty_Fun (Ty_Builtin
    DefaultUniInteger) (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Builtin
    DefaultUniBool)))) (Builtin EqualsInteger)) Nil) (Let NonRec (Cons
    (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XO (XI (XI (XI (XO XH)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniData) (Ty_Fun (Ty_Builtin DefaultUniData) (Ty_Builtin
    DefaultUniBool)))) (Builtin EqualsData)) Nil) (Let NonRec (Cons (TermBind
    Strict (VarDecl (show_Z (Zpos (XI (XI (XI (XO (XO XH))))))) (Ty_Fun
    (Ty_Builtin DefaultUniByteString) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Builtin DefaultUniBool)))) (Builtin
    EqualsByteString)) Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XI (XO (XO (XI XH))))))) (Ty_Fun (Ty_Builtin
    DefaultUniString) (Ty_Builtin DefaultUniByteString))) (Builtin
    EncodeUtf8)) Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XI (XO (XO XH)))))) (Ty_Builtin DefaultUniString))
    (Constant0 (some (ValueOf DefaultUniString (unsafeCoerce Nil))))) Nil)
    (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XI (XO (XO XH)))))) (Ty_Builtin DefaultUniByteString))
    (Constant0 (some (ValueOf DefaultUniByteString (unsafeCoerce Nil)))))
    Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XI (XO (XI XH)))))) (Ty_Fun (Ty_Builtin
    DefaultUniInteger) (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Builtin
    DefaultUniInteger)))) (Builtin DivideInteger)) Nil) (Let NonRec (Cons
    (TermBind Strict (VarDecl (show_Z (Zpos (XI (XI (XO (XO (XI XH)))))))
    (Ty_Fun (Ty_Builtin DefaultUniByteString) (Ty_Builtin DefaultUniString)))
    (Builtin DecodeUtf8)) Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XI (XI (XI (XI (XI XH)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Builtin DefaultUniInteger))) (Builtin
    countSetBits)) Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XI (XO (XO (XO XH))))))) (Ty_Fun (Ty_Builtin
    DefaultUniInteger) (Ty_Fun (Ty_Builtin DefaultUniByteString) (Ty_Builtin
    DefaultUniByteString)))) (Builtin ConsByteString)) Nil) (Let NonRec (Cons
    (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XO (XO (XI (XI (XI XH)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Builtin DefaultUniByteString))) (Builtin
    complementByteString)) Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XI (XI (XO (XI XH))))))) (Ty_Forall
    (show_Z (Zpos (XO (XI (XI (XO (XI XH))))))) Kind_Base (Ty_Fun (Ty_Builtin
    DefaultUniUnit) (Ty_Fun (Ty_Var
    (show_Z (Zpos (XO (XI (XI (XO (XI XH)))))))) (Ty_Var
    (show_Z (Zpos (XO (XI (XI (XO (XI XH)))))))))))) (Builtin ChooseUnit))
    Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XI (XO (XO (XO (XO XH)))))))) (Ty_Forall
    (show_Z (Zpos (XO (XO (XO (XO (XO (XO XH)))))))) Kind_Base (Ty_Forall
    (show_Z (Zpos (XI (XO (XO (XO (XO (XO XH)))))))) Kind_Base (Ty_Fun
    (Ty_App (Ty_Builtin DefaultUniProtoList) (Ty_Var
    (show_Z (Zpos (XO (XO (XO (XO (XO (XO XH)))))))))) (Ty_Fun (Ty_Var
    (show_Z (Zpos (XI (XO (XO (XO (XO (XO XH))))))))) (Ty_Fun (Ty_Var
    (show_Z (Zpos (XI (XO (XO (XO (XO (XO XH))))))))) (Ty_Var
    (show_Z (Zpos (XI (XO (XO (XO (XO (XO XH))))))))))))))) (Builtin
    ChooseList)) Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XI (XI (XI (XO (XO XH)))))))) (Ty_Forall
    (show_Z (Zpos (XO (XI (XI (XI (XO (XO XH)))))))) Kind_Base (Ty_Fun
    (Ty_Builtin DefaultUniData) (Ty_Fun (Ty_Var
    (show_Z (Zpos (XO (XI (XI (XI (XO (XO XH))))))))) (Ty_Fun (Ty_Var
    (show_Z (Zpos (XO (XI (XI (XI (XO (XO XH))))))))) (Ty_Fun (Ty_Var
    (show_Z (Zpos (XO (XI (XI (XI (XO (XO XH))))))))) (Ty_Fun (Ty_Var
    (show_Z (Zpos (XO (XI (XI (XI (XO (XO XH))))))))) (Ty_Fun (Ty_Var
    (show_Z (Zpos (XO (XI (XI (XI (XO (XO XH))))))))) (Ty_Var
    (show_Z (Zpos (XO (XI (XI (XI (XO (XO XH))))))))))))))))) (Builtin
    ChooseData)) Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XO (XO (XO (XI (XO XH)))))))) (Ty_Forall
    (show_Z (Zpos (XO (XO (XO (XO (XI (XO XH)))))))) Kind_Base (Ty_Fun
    (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Fun (Ty_App (Ty_Builtin
    DefaultUniProtoList) (Ty_Builtin DefaultUniData)) (Ty_Var
    (show_Z (Zpos (XO (XO (XO (XO (XI (XO XH))))))))))) (Ty_Fun (Ty_Fun
    (Ty_App (Ty_Builtin DefaultUniProtoList) (Ty_App (Ty_App (Ty_Builtin
    DefaultUniProtoPair) (Ty_Builtin DefaultUniData)) (Ty_Builtin
    DefaultUniData))) (Ty_Var
    (show_Z (Zpos (XO (XO (XO (XO (XI (XO XH)))))))))) (Ty_Fun (Ty_Fun
    (Ty_App (Ty_Builtin DefaultUniProtoList) (Ty_Builtin DefaultUniData))
    (Ty_Var (show_Z (Zpos (XO (XO (XO (XO (XI (XO XH)))))))))) (Ty_Fun
    (Ty_Fun (Ty_Builtin DefaultUniInteger) (Ty_Var
    (show_Z (Zpos (XO (XO (XO (XO (XI (XO XH)))))))))) (Ty_Fun (Ty_Fun
    (Ty_Builtin DefaultUniByteString) (Ty_Var
    (show_Z (Zpos (XO (XO (XO (XO (XI (XO XH)))))))))) (Ty_Fun (Ty_Builtin
    DefaultUniData) (Ty_Var
    (show_Z (Zpos (XO (XO (XO (XO (XI (XO XH))))))))))))))))) (TyAbs
    (show_Z Z0) Kind_Base (LamAbs (show_Z (Zpos (XO XH))) (Ty_Fun (Ty_Builtin
    DefaultUniInteger) (Ty_Fun (Ty_App (Ty_Builtin DefaultUniProtoList)
    (Ty_Builtin DefaultUniData)) (Ty_Var (show_Z Z0)))) (LamAbs
    (show_Z (Zpos (XI XH))) (Ty_Fun (Ty_App (Ty_Builtin DefaultUniProtoList)
    (Ty_App (Ty_App (Ty_Builtin DefaultUniProtoPair) (Ty_Builtin
    DefaultUniData)) (Ty_Builtin DefaultUniData))) (Ty_Var (show_Z Z0)))
    (LamAbs (show_Z (Zpos (XO (XO XH)))) (Ty_Fun (Ty_App (Ty_Builtin
    DefaultUniProtoList) (Ty_Builtin DefaultUniData)) (Ty_Var (show_Z Z0)))
    (LamAbs (show_Z (Zpos (XI (XO XH)))) (Ty_Fun (Ty_Builtin
    DefaultUniInteger) (Ty_Var (show_Z Z0))) (LamAbs
    (show_Z (Zpos (XO (XI XH)))) (Ty_Fun (Ty_Builtin DefaultUniByteString)
    (Ty_Var (show_Z Z0))) (LamAbs (show_Z (Zpos (XI (XI XH)))) (Ty_Builtin
    DefaultUniData) (TyInst (Apply (Apply (Apply (Apply (Apply (Apply (TyInst
    (Builtin ChooseData) (Ty_Forall (show_Z (Zpos XH)) Kind_Base (Ty_Var
    (show_Z Z0)))) (Var (show_Z (Zpos (XI (XI XH)))))) (TyAbs
    (show_Z (Zpos XH)) Kind_Base (Apply (Apply (TyInst (TyInst (TyInst (TyAbs
    (show_Z Z0) Kind_Base (TyAbs (show_Z (Zpos XH)) Kind_Base (TyAbs
    (show_Z (Zpos (XO XH))) Kind_Base (LamAbs (show_Z (Zpos (XI XH))) (Ty_Fun
    (Ty_Var (show_Z Z0)) (Ty_Fun (Ty_Var (show_Z (Zpos XH))) (Ty_Var
    (show_Z (Zpos (XO XH)))))) (LamAbs (show_Z (Zpos (XO (XO XH)))) (Ty_App
    (Ty_App (Ty_Builtin DefaultUniProtoPair) (Ty_Var (show_Z Z0))) (Ty_Var
    (show_Z (Zpos XH)))) (Apply (Apply (Var (show_Z (Zpos (XI XH)))) (Apply
    (TyInst (TyInst (Builtin FstPair) (Ty_Var (show_Z Z0))) (Ty_Var
    (show_Z (Zpos XH)))) (Var (show_Z (Zpos (XO (XO XH))))))) (Apply (TyInst
    (TyInst (Builtin SndPair) (Ty_Var (show_Z Z0))) (Ty_Var
    (show_Z (Zpos XH)))) (Var (show_Z (Zpos (XO (XO XH))))))))))))
    (Ty_Builtin DefaultUniInteger)) (Ty_App (Ty_Builtin DefaultUniProtoList)
    (Ty_Builtin DefaultUniData))) (Ty_Var (show_Z Z0))) (Var
    (show_Z (Zpos (XO XH))))) (Apply (Builtin UnConstrData) (Var
    (show_Z (Zpos (XI (XI XH))))))))) (TyAbs (show_Z (Zpos XH)) Kind_Base
    (Apply (Var (show_Z (Zpos (XI XH)))) (Apply (Builtin UnMapData) (Var
    (show_Z (Zpos (XI (XI XH))))))))) (TyAbs (show_Z (Zpos XH)) Kind_Base
    (Apply (Var (show_Z (Zpos (XO (XO XH))))) (Apply (Builtin UnListData)
    (Var (show_Z (Zpos (XI (XI XH))))))))) (TyAbs (show_Z (Zpos XH))
    Kind_Base (Apply (Var (show_Z (Zpos (XI (XO XH))))) (Apply (Builtin
    UnIData) (Var (show_Z (Zpos (XI (XI XH))))))))) (TyAbs (show_Z (Zpos XH))
    Kind_Base (Apply (Var (show_Z (Zpos (XO (XI XH))))) (Apply (Builtin
    UnBData) (Var (show_Z (Zpos (XI (XI XH))))))))) (Ty_Var
    (show_Z Z0))))))))))) Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XO (XI (XO (XI (XI XH)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniBool) (Ty_Fun (Ty_Builtin DefaultUniByteString) (Ty_Builtin
    DefaultUniInteger)))) (Builtin ByteStringToInteger)) Nil) (Let NonRec
    (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XO (XO (XO (XI (XI XH)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniBLS12_381_MlResult) (Ty_Fun (Ty_Builtin
    DefaultUniBLS12_381_MlResult) (Ty_Builtin
    DefaultUniBLS12_381_MlResult)))) (Builtin Bls12_381_mulMlResult)) Nil)
    (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XI (XI (XI (XO (XI XH)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniBLS12_381_G1_Element) (Ty_Fun (Ty_Builtin
    DefaultUniBLS12_381_G2_Element) (Ty_Builtin
    DefaultUniBLS12_381_MlResult)))) (Builtin Bls12_381_millerLoop)) Nil)
    (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XO (XO (XO (XI (XI XH)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniBLS12_381_MlResult) (Ty_Fun (Ty_Builtin
    DefaultUniBLS12_381_MlResult) (Ty_Builtin DefaultUniBool)))) (Builtin
    Bls12_381_finalVerify)) Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XI (XI (XI (XO (XI XH)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Builtin DefaultUniBLS12_381_G2_Element)))
    (Builtin Bls12_381_G2_uncompress)) Nil) (Let NonRec (Cons (TermBind
    Strict (VarDecl (show_Z (Zpos (XO (XI (XO (XI (XO (XI XH)))))))) (Ty_Fun
    (Ty_Builtin DefaultUniInteger) (Ty_Fun (Ty_Builtin
    DefaultUniBLS12_381_G2_Element) (Ty_Builtin
    DefaultUniBLS12_381_G2_Element)))) (Builtin Bls12_381_G2_scalarMul)) Nil)
    (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XO (XO (XI (XO (XI XH)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniBLS12_381_G2_Element) (Ty_Builtin
    DefaultUniBLS12_381_G2_Element))) (Builtin Bls12_381_G2_neg)) Nil) (Let
    NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XO (XI (XI (XO (XI XH)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Fun (Ty_Builtin DefaultUniByteString)
    (Ty_Builtin DefaultUniBLS12_381_G2_Element)))) (Builtin
    Bls12_381_G2_hashToGroup)) Nil) (Let NonRec (Cons (TermBind Strict
    (VarDecl (show_Z (Zpos (XI (XI (XO (XI (XO (XI XH)))))))) (Ty_Fun
    (Ty_Builtin DefaultUniBLS12_381_G2_Element) (Ty_Fun (Ty_Builtin
    DefaultUniBLS12_381_G2_Element) (Ty_Builtin DefaultUniBool)))) (Builtin
    Bls12_381_G2_equal)) Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XI (XI (XO XH)))))) (Ty_Builtin DefaultUniByteString))
    (Constant0
    (some (ValueOf DefaultUniByteString
      (unsafeCoerce (Cons Xc0 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons
        X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons
        X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons
        X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons
        X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons
        X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons
        X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons
        X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons
        X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons
        X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons
        X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons
        X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons
        X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons
        X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00
        Nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XI (XI (XO XH)))))) (Ty_Builtin DefaultUniByteString))
    (Constant0
    (some (ValueOf DefaultUniByteString
      (unsafeCoerce (Cons X93 (Cons Xe0 (Cons X2b (Cons X60 (Cons X52 (Cons
        X71 (Cons X9f (Cons X60 (Cons X7d (Cons Xac (Cons Xd3 (Cons Xa0 (Cons
        X88 (Cons X27 (Cons X4f (Cons X65 (Cons X59 (Cons X6b (Cons Xd0 (Cons
        Xd0 (Cons X99 (Cons X20 (Cons Xb6 (Cons X1a (Cons Xb5 (Cons Xda (Cons
        X61 (Cons Xbb (Cons Xdc (Cons X7f (Cons X50 (Cons X49 (Cons X33 (Cons
        X4c (Cons Xf1 (Cons X12 (Cons X13 (Cons X94 (Cons X5d (Cons X57 (Cons
        Xe5 (Cons Xac (Cons X7d (Cons X05 (Cons X5d (Cons X04 (Cons X2b (Cons
        X7e (Cons X02 (Cons X4a (Cons Xa2 (Cons Xb2 (Cons Xf0 (Cons X8f (Cons
        X0a (Cons X91 (Cons X26 (Cons X08 (Cons X05 (Cons X27 (Cons X2d (Cons
        Xc5 (Cons X10 (Cons X51 (Cons Xc6 (Cons Xe4 (Cons X7a (Cons Xd4 (Cons
        Xfa (Cons X40 (Cons X3b (Cons X02 (Cons Xb4 (Cons X51 (Cons X0b (Cons
        X64 (Cons X7a (Cons Xe3 (Cons Xd1 (Cons X77 (Cons X0b (Cons Xac (Cons
        X03 (Cons X26 (Cons Xa8 (Cons X05 (Cons Xbb (Cons Xef (Cons Xd4 (Cons
        X80 (Cons X56 (Cons Xc8 (Cons Xc1 (Cons X21 (Cons Xbd (Cons Xb8
        Nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XO (XI (XI (XO (XI XH)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniBLS12_381_G2_Element) (Ty_Builtin DefaultUniByteString)))
    (Builtin Bls12_381_G2_compress)) Nil) (Let NonRec (Cons (TermBind Strict
    (VarDecl (show_Z (Zpos (XO (XO (XO (XI (XO (XI XH)))))))) (Ty_Fun
    (Ty_Builtin DefaultUniBLS12_381_G2_Element) (Ty_Fun (Ty_Builtin
    DefaultUniBLS12_381_G2_Element) (Ty_Builtin
    DefaultUniBLS12_381_G2_Element)))) (Builtin Bls12_381_G2_add)) Nil) (Let
    NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XI (XI (XO (XO (XI XH)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Builtin DefaultUniBLS12_381_G1_Element)))
    (Builtin Bls12_381_G1_uncompress)) Nil) (Let NonRec (Cons (TermBind
    Strict (VarDecl (show_Z (Zpos (XI (XI (XO (XO (XO (XI XH)))))))) (Ty_Fun
    (Ty_Builtin DefaultUniInteger) (Ty_Fun (Ty_Builtin
    DefaultUniBLS12_381_G1_Element) (Ty_Builtin
    DefaultUniBLS12_381_G1_Element)))) (Builtin Bls12_381_G1_scalarMul)) Nil)
    (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XI (XO (XO (XO (XI XH)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniBLS12_381_G1_Element) (Ty_Builtin
    DefaultUniBLS12_381_G1_Element))) (Builtin Bls12_381_G1_neg)) Nil) (Let
    NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XO (XI (XO (XO (XI XH)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Fun (Ty_Builtin DefaultUniByteString)
    (Ty_Builtin DefaultUniBLS12_381_G1_Element)))) (Builtin
    Bls12_381_G1_hashToGroup)) Nil) (Let NonRec (Cons (TermBind Strict
    (VarDecl (show_Z (Zpos (XO (XO (XI (XO (XO (XI XH)))))))) (Ty_Fun
    (Ty_Builtin DefaultUniBLS12_381_G1_Element) (Ty_Fun (Ty_Builtin
    DefaultUniBLS12_381_G1_Element) (Ty_Builtin DefaultUniBool)))) (Builtin
    Bls12_381_G1_equal)) Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XO (XI (XO XH)))))) (Ty_Builtin DefaultUniByteString))
    (Constant0
    (some (ValueOf DefaultUniByteString
      (unsafeCoerce (Cons Xc0 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons
        X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons
        X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons
        X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons
        X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons
        X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons
        X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons X00 (Cons
        X00 Nil))))))))))))))))))))))))))))))))))))))))))))))))))))) Nil)
    (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XO (XI (XO XH)))))) (Ty_Builtin DefaultUniByteString))
    (Constant0
    (some (ValueOf DefaultUniByteString
      (unsafeCoerce (Cons X97 (Cons Xf1 (Cons Xd3 (Cons Xa7 (Cons X31 (Cons
        X97 (Cons Xd7 (Cons X94 (Cons X26 (Cons X95 (Cons X63 (Cons X8c (Cons
        X4f (Cons Xa9 (Cons Xac (Cons X0f (Cons Xc3 (Cons X68 (Cons X8c (Cons
        X4f (Cons X97 (Cons X74 (Cons Xb9 (Cons X05 (Cons Xa1 (Cons X4e (Cons
        X3a (Cons X3f (Cons X17 (Cons X1b (Cons Xac (Cons X58 (Cons X6c (Cons
        X55 (Cons Xe8 (Cons X3f (Cons Xf9 (Cons X7a (Cons X1a (Cons Xef (Cons
        Xfb (Cons X3a (Cons Xf0 (Cons X0a (Cons Xdb (Cons X22 (Cons Xc6 (Cons
        Xbb Nil))))))))))))))))))))))))))))))))))))))))))))))))))))) Nil)
    (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XI (XI (XO (XO (XI XH)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniBLS12_381_G1_Element) (Ty_Builtin DefaultUniByteString)))
    (Builtin Bls12_381_G1_compress)) Nil) (Let NonRec (Cons (TermBind Strict
    (VarDecl (show_Z (Zpos (XI (XO (XO (XO (XO (XI XH)))))))) (Ty_Fun
    (Ty_Builtin DefaultUniBLS12_381_G1_Element) (Ty_Fun (Ty_Builtin
    DefaultUniBLS12_381_G1_Element) (Ty_Builtin
    DefaultUniBLS12_381_G1_Element)))) (Builtin Bls12_381_G1_add)) Nil) (Let
    NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XO (XI (XI (XO XH))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Builtin DefaultUniByteString))) (Builtin
    Blake2b_256)) Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XI (XI (XO (XO (XI (XI XH)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Builtin DefaultUniByteString))) (Builtin
    Blake2b_224)) Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XO (XO (XO (XI XH))))))) (Ty_Fun (Ty_Builtin
    DefaultUniString) (Ty_Fun (Ty_Builtin DefaultUniString) (Ty_Builtin
    DefaultUniString)))) (Builtin AppendString)) Nil) (Let NonRec (Cons
    (TermBind Strict (VarDecl (show_Z (Zpos (XO (XI (XO (XO (XO XH)))))))
    (Ty_Fun (Ty_Builtin DefaultUniByteString) (Ty_Fun (Ty_Builtin
    DefaultUniByteString) (Ty_Builtin DefaultUniByteString)))) (Builtin
    AppendByteString)) Nil) (Let NonRec (Cons (TermBind Strict (VarDecl
    (show_Z (Zpos (XO (XI (XI (XO (XI (XI XH)))))))) (Ty_Fun (Ty_Builtin
    DefaultUniBool) (Ty_Fun (Ty_Builtin DefaultUniByteString) (Ty_Fun
    (Ty_Builtin DefaultUniByteString) (Ty_Builtin DefaultUniByteString)))))
    (Builtin andByteString)) Nil) (Let NonRec (Cons (TypeBind (TyVarDecl
    (show_Z (Zpos (XI XH))) Kind_Base) (Ty_Builtin DefaultUniUnit)) Nil) (Let
    NonRec (Cons (TypeBind (TyVarDecl (show_Z (Zpos (XO (XO XH)))) Kind_Base)
    (Ty_Builtin DefaultUniString)) Nil) (Let NonRec (Cons (TypeBind
    (TyVarDecl (show_Z (Zpos (XO (XI XH)))) (Kind_Arrow Kind_Base (Kind_Arrow
    Kind_Base Kind_Base))) (Ty_Builtin DefaultUniProtoPair)) Nil) (Let NonRec
    (Cons (TypeBind (TyVarDecl (show_Z Z0) Kind_Base) (Ty_Builtin
    DefaultUniByteString)) Nil) (Let NonRec (Cons (TypeBind (TyVarDecl
    (show_Z (Zpos (XO XH))) Kind_Base) (Ty_Builtin DefaultUniBool)) Nil) (Let
    NonRec (Cons (TypeBind (TyVarDecl (show_Z (Zpos (XO (XI (XO XH)))))
    Kind_Base) (Ty_Builtin DefaultUniBLS12_381_MlResult)) Nil) (Let NonRec
    (Cons (TypeBind (TyVarDecl (show_Z (Zpos (XI (XO (XO XH))))) Kind_Base)
    (Ty_Builtin DefaultUniBLS12_381_G2_Element)) Nil) (Let NonRec (Cons
    (TypeBind (TyVarDecl (show_Z (Zpos (XO (XO (XO XH))))) Kind_Base)
    (Ty_Builtin DefaultUniBLS12_381_G1_Element)) Nil) (TyInst (Var
    (show_Z (Zpos (XO (XO (XO (XI (XO (XO (XO XH)))))))))) (Ty_Builtin
    DefaultUniInteger))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

main :: Prelude.IO ()
main = Prelude.return ()