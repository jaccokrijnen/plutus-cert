{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Main where

import qualified Prelude
import qualified GHC.Exts



import qualified GHC.Base


unsafeCoerce :: a -> b
unsafeCoerce = GHC.Exts.unsafeCoerce#


type Any = GHC.Base.Any


__ :: any
__ = Prelude.error "Logical or arity value used"

false_rec :: a1
false_rec =
  Prelude.error "absurd case"

data Bool =
   True
 | False
 deriving (Prelude.Show)
 

bool_rect :: a1 -> a1 -> Bool -> a1
bool_rect f f0 b =
  case b of {
   True -> f;
   False -> f0}

bool_rec :: a1 -> a1 -> Bool -> a1
bool_rec =
  bool_rect

andb :: Bool -> Bool -> Bool
andb b1 b2 =
  case b1 of {
   True -> b2;
   False -> False}

orb :: Bool -> Bool -> Bool
orb b1 b2 =
  case b1 of {
   True -> True;
   False -> b2}

data Nat =
   O
 | S Nat

data Option a =
   Some a
 | None

data Sum a b =
   Inl a
 | Inr b

data Prod a b =
   Pair a b

data List a =
   Nil
 | Cons a (List a)

app :: (List a1) -> (List a1) -> List a1
app l m =
  case l of {
   Nil -> m;
   Cons a l1 -> Cons a (app l1 m)}

data SigT a p =
   ExistT a p

data Sumbool =
   Left
 | Right

sumbool_rect :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rect f f0 s =
  case s of {
   Left -> f __;
   Right -> f0 __}

sumbool_rec :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rec =
  sumbool_rect

bool_dec :: Bool -> Bool -> Sumbool
bool_dec b1 b2 =
  bool_rec (\x -> case x of {
                   True -> Left;
                   False -> Right}) (\x ->
    case x of {
     True -> Right;
     False -> Left}) b1 b2

eqb :: Bool -> Bool -> Bool
eqb b1 b2 =
  case b1 of {
   True -> b2;
   False -> case b2 of {
             True -> False;
             False -> True}}

remove :: (a1 -> a1 -> Sumbool) -> a1 -> (List a1) -> List a1
remove eq_dec x l =
  case l of {
   Nil -> Nil;
   Cons y tl ->
    case eq_dec x y of {
     Left -> remove eq_dec x tl;
     Right -> Cons y (remove eq_dec x tl)}}

existsb :: (a1 -> Bool) -> (List a1) -> Bool
existsb f l =
  case l of {
   Nil -> False;
   Cons a l0 -> orb (f a) (existsb f l0)}

data Ascii0 =
   Ascii Bool Bool Bool Bool Bool Bool Bool Bool
   deriving (Prelude.Show)

ascii_rect :: (Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool
              -> a1) -> Ascii0 -> a1
ascii_rect f a =
  case a of {
   Ascii b b0 b1 b2 b3 b4 b5 b6 -> f b b0 b1 b2 b3 b4 b5 b6}

ascii_rec :: (Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool ->
             a1) -> Ascii0 -> a1
ascii_rec =
  ascii_rect

ascii_dec :: Ascii0 -> Ascii0 -> Sumbool
ascii_dec a b =
  ascii_rec (\b0 b1 b2 b3 b4 b5 b6 b7 x ->
    case x of {
     Ascii b8 b9 b10 b11 b12 b13 b14 b15 ->
      sumbool_rec (\_ ->
        sumbool_rec (\_ ->
          sumbool_rec (\_ ->
            sumbool_rec (\_ ->
              sumbool_rec (\_ ->
                sumbool_rec (\_ ->
                  sumbool_rec (\_ ->
                    sumbool_rec (\_ -> Left) (\_ -> Right) (bool_dec b7 b15))
                    (\_ -> Right) (bool_dec b6 b14)) (\_ -> Right)
                  (bool_dec b5 b13)) (\_ -> Right) (bool_dec b4 b12)) (\_ ->
              Right) (bool_dec b3 b11)) (\_ -> Right) (bool_dec b2 b10))
          (\_ -> Right) (bool_dec b1 b9)) (\_ -> Right) (bool_dec b0 b8)}) a
    b

eqb0 :: Ascii0 -> Ascii0 -> Bool
eqb0 a b =
  case a of {
   Ascii a0 a1 a2 a3 a4 a5 a6 a7 ->
    case b of {
     Ascii b0 b1 b2 b3 b4 b5 b6 b7 ->
      case case case case case case case eqb a0 b0 of {
                                     True -> eqb a1 b1;
                                     False -> False} of {
                                True -> eqb a2 b2;
                                False -> False} of {
                           True -> eqb a3 b3;
                           False -> False} of {
                      True -> eqb a4 b4;
                      False -> False} of {
                 True -> eqb a5 b5;
                 False -> False} of {
            True -> eqb a6 b6;
            False -> False} of {
       True -> eqb a7 b7;
       False -> False}}}

data String =
   EmptyString
 | String0 Ascii0 String
 deriving (Prelude.Show)

string_rect :: a1 -> (Ascii0 -> String -> a1 -> a1) -> String -> a1
string_rect f f0 s =
  case s of {
   EmptyString -> f;
   String0 a s0 -> f0 a s0 (string_rect f f0 s0)}

string_rec :: a1 -> (Ascii0 -> String -> a1 -> a1) -> String -> a1
string_rec =
  string_rect

string_dec :: String -> String -> Sumbool
string_dec s1 s2 =
  string_rec (\x -> case x of {
                     EmptyString -> Left;
                     String0 _ _ -> Right}) (\a _ x x0 ->
    case x0 of {
     EmptyString -> Right;
     String0 a0 s ->
      sumbool_rec (\_ -> sumbool_rec (\_ -> Left) (\_ -> Right) (x s)) (\_ ->
        Right) (ascii_dec a a0)}) s1 s2

eqb1 :: String -> String -> Bool
eqb1 s1 s2 =
  case s1 of {
   EmptyString -> case s2 of {
                   EmptyString -> True;
                   String0 _ _ -> False};
   String0 c1 s1' ->
    case s2 of {
     EmptyString -> False;
     String0 c2 s2' ->
      case eqb0 c1 c2 of {
       True -> eqb1 s1' s2';
       False -> False}}}

append :: String -> String -> String
append s1 s2 =
  case s1 of {
   EmptyString -> s2;
   String0 c s1' -> String0 c (append s1' s2)}

concat :: String -> (List String) -> String
concat sep ls =
  case ls of {
   Nil -> EmptyString;
   Cons x xs ->
    case xs of {
     Nil -> x;
     Cons _ _ -> append x (append sep (concat sep xs))}}

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
 deriving (Prelude.Show)

type Tyname = String

type BinderTyname = String

data Kind =
   Kind_Base
 | Kind_Arrow Kind Kind
 deriving (Prelude.Show)

kind_rect :: a1 -> (Kind -> a1 -> Kind -> a1 -> a1) -> Kind -> a1
kind_rect f f0 k =
  case k of {
   Kind_Base -> f;
   Kind_Arrow k0 k1 -> f0 k0 (kind_rect f f0 k0) k1 (kind_rect f f0 k1)}

kind_rec :: a1 -> (Kind -> a1 -> Kind -> a1 -> a1) -> Kind -> a1
kind_rec =
  kind_rect

data Ty =
   Ty_Var Tyname
 | Ty_Fun Ty Ty
 | Ty_IFix Ty Ty
 | Ty_Forall BinderTyname Kind Ty
 | Ty_Builtin DefaultUni
 | Ty_Lam BinderTyname Kind Ty
 | Ty_App Ty Ty
 deriving (Prelude.Show)


ty_rect :: (Tyname -> a1) -> (Ty -> a1 -> Ty -> a1 -> a1) -> (Ty -> a1 -> Ty
           -> a1 -> a1) -> (BinderTyname -> Kind -> Ty -> a1 -> a1) ->
           (DefaultUni -> a1) -> (BinderTyname -> Kind -> Ty -> a1 -> a1) ->
           (Ty -> a1 -> Ty -> a1 -> a1) -> Ty -> a1
ty_rect f f0 f1 f2 f3 f4 f5 t =
  case t of {
   Ty_Var t0 -> f t0;
   Ty_Fun t0 t1 ->
    f0 t0 (ty_rect f f0 f1 f2 f3 f4 f5 t0) t1
      (ty_rect f f0 f1 f2 f3 f4 f5 t1);
   Ty_IFix t0 t1 ->
    f1 t0 (ty_rect f f0 f1 f2 f3 f4 f5 t0) t1
      (ty_rect f f0 f1 f2 f3 f4 f5 t1);
   Ty_Forall b k t0 -> f2 b k t0 (ty_rect f f0 f1 f2 f3 f4 f5 t0);
   Ty_Builtin d -> f3 d;
   Ty_Lam b k t0 -> f4 b k t0 (ty_rect f f0 f1 f2 f3 f4 f5 t0);
   Ty_App t0 t1 ->
    f5 t0 (ty_rect f f0 f1 f2 f3 f4 f5 t0) t1
      (ty_rect f f0 f1 f2 f3 f4 f5 t1)}

ty_rec :: (Tyname -> a1) -> (Ty -> a1 -> Ty -> a1 -> a1) -> (Ty -> a1 -> Ty
          -> a1 -> a1) -> (BinderTyname -> Kind -> Ty -> a1 -> a1) ->
          (DefaultUni -> a1) -> (BinderTyname -> Kind -> Ty -> a1 -> a1) ->
          (Ty -> a1 -> Ty -> a1 -> a1) -> Ty -> a1
ty_rec =
  ty_rect

lookup :: String -> (List (Prod String a1)) -> Option a1
lookup k l =
  case l of {
   Nil -> None;
   Cons p l' ->
    case p of {
     Pair j x -> case eqb1 j k of {
                  True -> Some x;
                  False -> lookup k l'}}}

ftv :: Ty -> List String
ftv t =
  case t of {
   Ty_Var x -> Cons x Nil;
   Ty_Fun t1 t2 -> app (ftv t1) (ftv t2);
   Ty_IFix f t0 -> app (ftv f) (ftv t0);
   Ty_Forall x _ t' -> remove string_dec x (ftv t');
   Ty_Builtin _ -> Nil;
   Ty_Lam x _ t' -> remove string_dec x (ftv t');
   Ty_App t1 t2 -> app (ftv t1) (ftv t2)}

substituteT :: String -> Ty -> Ty -> Ty
substituteT x u t =
  case t of {
   Ty_Var y -> case eqb1 x y of {
                True -> u;
                False -> Ty_Var y};
   Ty_Fun t1 t2 -> Ty_Fun (substituteT x u t1) (substituteT x u t2);
   Ty_IFix f t0 -> Ty_IFix (substituteT x u f) (substituteT x u t0);
   Ty_Forall y k t' ->
    case eqb1 x y of {
     True -> Ty_Forall y k t';
     False -> Ty_Forall y k (substituteT x u t')};
   Ty_Builtin u0 -> Ty_Builtin u0;
   Ty_Lam y k1 t' ->
    case eqb1 x y of {
     True -> Ty_Lam y k1 t';
     False -> Ty_Lam y k1 (substituteT x u t')};
   Ty_App t1 t2 -> Ty_App (substituteT x u t1) (substituteT x u t2)}

ftv0 :: Ty -> List String
ftv0 =
  ftv

fresh :: String -> Ty -> Ty -> String
fresh x u t =
  append (String0 (Ascii True False False False False True True False)
    EmptyString)
    (append x
      (append (concat EmptyString (ftv0 u)) (concat EmptyString (ftv0 t))))

rename :: String -> String -> Ty -> Ty
rename x y t =
  substituteT x (Ty_Var y) t

substituteTCA :: String -> Ty -> Ty -> Ty
substituteTCA a a0 b =
  let {
   fix_F x =
     let {x0 = case x of {
                (,) pr1 _ -> pr1}} in
     let {u = case case x of {
                    (,) _ pr2 -> pr2} of {
               (,) pr1 _ -> pr1}} in
     let {
      substituteTCA0 = \a1 a2 b0 ->
       let {y = (,) a1 ((,) a2 b0)} in (\_ -> fix_F y)}
     in
     case case case x of {
                (,) _ pr2 -> pr2} of {
           (,) _ pr2 -> pr2} of {
      Ty_Var t -> case eqb1 x0 t of {
                   True -> u;
                   False -> Ty_Var t};
      Ty_Fun t t0 -> Ty_Fun (substituteTCA0 x0 u t __)
       (substituteTCA0 x0 u t0 __);
      Ty_IFix t t0 -> Ty_IFix (substituteTCA0 x0 u t __)
       (substituteTCA0 x0 u t0 __);
      Ty_Forall b0 k t ->
       case eqb1 x0 b0 of {
        True -> Ty_Forall b0 k t;
        False ->
         case existsb (eqb1 b0) (ftv0 u) of {
          True ->
           let {y' = fresh x0 u t} in
           let {t' = rename b0 y' t} in
           Ty_Forall y' k (substituteTCA0 x0 u t' __);
          False -> Ty_Forall b0 k t}};
      Ty_Builtin d -> Ty_Builtin d;
      Ty_Lam b0 k t ->
       case eqb1 x0 b0 of {
        True -> Ty_Lam b0 k t;
        False ->
         case existsb (eqb1 b0) (ftv0 u) of {
          True ->
           let {y' = fresh x0 u t} in
           let {t' = rename b0 y' t} in
           Ty_Lam y' k (substituteTCA0 x0 u t' __);
          False -> Ty_Lam b0 k (substituteTCA0 x0 u t __)}};
      Ty_App t t0 -> Ty_App (substituteTCA0 x0 u t __)
       (substituteTCA0 x0 u t0 __)}}
  in fix_F ((,) a ((,) a0 b))

data Step =
   Step_beta String Kind Ty Ty
 | Step_appL Ty Ty Ty Step
 | Step_appR Ty Ty Ty Step
 | Step_funL Ty Ty Ty Step
 | Step_funR Ty Ty Ty Step
 | Step_forall BinderTyname Kind Ty Ty Step
 | Step_abs BinderTyname Kind Ty Ty Step
 | Step_ifixL Ty Ty Ty Step
 | Step_ifixR Ty Ty Ty Step

type EqDec a = a -> a -> Sumbool

kind_dec :: EqDec Kind
kind_dec x y =
  kind_rec (\x0 -> case x0 of {
                    Kind_Base -> Left;
                    Kind_Arrow _ _ -> Right}) (\_ x0 _ x1 x2 ->
    case x2 of {
     Kind_Base -> Right;
     Kind_Arrow k k0 ->
      sumbool_rec (\_ -> sumbool_rec (\_ -> Left) (\_ -> Right) (x1 k0))
        (\_ -> Right) (x0 k)}) x y

type Eqb x = x -> x -> Bool

eq_dec_to_eqb :: (EqDec a1) -> Eqb a1
eq_dec_to_eqb dec_eq x y =
  case dec_eq x y of {
   Left -> True;
   Right -> False}

kind_eqb :: Eqb Kind
kind_eqb =
  eq_dec_to_eqb kind_dec

kind_check_default_uni :: DefaultUni -> Option Kind
kind_check_default_uni d =
  case d of {
   DefaultUniProtoList -> Some (Kind_Arrow Kind_Base Kind_Base);
   DefaultUniProtoPair -> Some (Kind_Arrow Kind_Base (Kind_Arrow Kind_Base
    Kind_Base));
   DefaultUniApply t t' ->
    let {o = kind_check_default_uni t} in
    let {o0 = kind_check_default_uni t'} in
    case o of {
     Some k0 ->
      case k0 of {
       Kind_Base -> None;
       Kind_Arrow k k' ->
        case o0 of {
         Some k'' -> case kind_eqb k'' k of {
                      True -> Some k';
                      False -> None};
         None -> None}};
     None -> None};
   _ -> Some Kind_Base}

kind_check :: (List (Prod BinderTyname Kind)) -> Ty -> Option Kind
kind_check delta ty =
  case ty of {
   Ty_Var x -> lookup x delta;
   Ty_Fun t1 t2 ->
    let {o = kind_check delta t1} in
    let {o0 = kind_check delta t2} in
    case o of {
     Some k ->
      case k of {
       Kind_Base ->
        case o0 of {
         Some k0 ->
          case k0 of {
           Kind_Base -> Some Kind_Base;
           Kind_Arrow _ _ -> None};
         None -> None};
       Kind_Arrow _ _ -> None};
     None -> None};
   Ty_IFix f t ->
    case kind_check delta t of {
     Some k ->
      case kind_check delta f of {
       Some k0 ->
        case k0 of {
         Kind_Base -> None;
         Kind_Arrow k1 k2 ->
          case k1 of {
           Kind_Base -> None;
           Kind_Arrow k3 k4 ->
            case k4 of {
             Kind_Base ->
              case k2 of {
               Kind_Base -> None;
               Kind_Arrow k5 k6 ->
                case k6 of {
                 Kind_Base ->
                  case andb (kind_eqb k k3) (kind_eqb k k5) of {
                   True -> Some Kind_Base;
                   False -> None};
                 Kind_Arrow _ _ -> None}};
             Kind_Arrow _ _ -> None}}};
       None -> None};
     None -> None};
   Ty_Forall x k t ->
    case kind_check (Cons (Pair x k) delta) t of {
     Some k0 ->
      case k0 of {
       Kind_Base -> Some Kind_Base;
       Kind_Arrow _ _ -> None};
     None -> None};
   Ty_Builtin d ->
    case kind_check_default_uni d of {
     Some k ->
      case k of {
       Kind_Base -> Some Kind_Base;
       Kind_Arrow _ _ -> None};
     None -> None};
   Ty_Lam x k1 t ->
    case kind_check (Cons (Pair x k1) delta) t of {
     Some k2 -> Some (Kind_Arrow k1 k2);
     None -> None};
   Ty_App t1 t2 ->
    let {o = kind_check delta t1} in
    let {o0 = kind_check delta t2} in
    case o of {
     Some k ->
      case k of {
       Kind_Base -> None;
       Kind_Arrow k11 k2 ->
        case o0 of {
         Some k12 ->
          case kind_eqb k11 k12 of {
           True -> Some k2;
           False -> None};
         None -> None}};
     None -> None}}

step_dec :: Ty -> (List (Prod BinderTyname Kind)) -> Kind -> Sum
            (SigT Ty Step) ()
step_dec t _UU0394_ k =
  ty_rec (\_ _ _ _ -> Inr __) (\t1 iHT1 t2 iHT2 _UU0394_0 _ _ ->
    let {o = kind_check _UU0394_0 t1} in
    case o of {
     Some k0 ->
      case k0 of {
       Kind_Base ->
        let {o0 = kind_check _UU0394_0 t2} in
        case o0 of {
         Some k1 ->
          case k1 of {
           Kind_Base ->
            let {s = iHT1 _UU0394_0 Kind_Base __} in
            case s of {
             Inl s0 -> Inl
              (case s0 of {
                ExistT x s1 -> ExistT (Ty_Fun x t2) (Step_funL t1 x t2 s1)});
             Inr _ ->
              let {s0 = iHT2 _UU0394_0 Kind_Base __} in
              case s0 of {
               Inl s1 -> Inl
                (case s1 of {
                  ExistT x s2 -> ExistT (Ty_Fun t1 x) (Step_funR t1 t2 x s2)});
               Inr _ -> Inr __}};
           Kind_Arrow _ _ -> false_rec};
         None -> false_rec};
       Kind_Arrow _ _ -> false_rec};
     None -> false_rec}) (\t1 iHT1 t2 iHT2 _UU0394_0 _ _ ->
    let {o = kind_check _UU0394_0 t2} in
    case o of {
     Some k0 ->
      let {o0 = kind_check _UU0394_0 t1} in
      case o0 of {
       Some k1 ->
        case k1 of {
         Kind_Base -> false_rec;
         Kind_Arrow k2 k3 ->
          case k2 of {
           Kind_Base -> false_rec;
           Kind_Arrow k4 k5 ->
            case k5 of {
             Kind_Base ->
              case k3 of {
               Kind_Base -> false_rec;
               Kind_Arrow k6 k7 ->
                case k7 of {
                 Kind_Base ->
                  let {b = andb (kind_eqb k0 k4) (kind_eqb k0 k6)} in
                  case b of {
                   True ->
                    let {
                     s = iHT1 _UU0394_0 (Kind_Arrow (Kind_Arrow k4 Kind_Base)
                           (Kind_Arrow k6 Kind_Base)) __}
                    in
                    case s of {
                     Inl s0 -> Inl
                      (case s0 of {
                        ExistT x s1 -> ExistT (Ty_IFix x t2) (Step_ifixL t1 x
                         t2 s1)});
                     Inr _ ->
                      let {s0 = iHT2 _UU0394_0 k0 __} in
                      case s0 of {
                       Inl s1 -> Inl
                        (case s1 of {
                          ExistT x s2 -> ExistT (Ty_IFix t1 x) (Step_ifixR t1
                           t2 x s2)});
                       Inr _ -> Inr __}};
                   False -> false_rec};
                 Kind_Arrow _ _ -> false_rec}};
             Kind_Arrow _ _ -> false_rec}}};
       None -> false_rec};
     None -> false_rec}) (\b k0 t0 iHT _UU0394_0 _ _ ->
    let {o = kind_check (Cons (Pair b k0) _UU0394_0) t0} in
    case o of {
     Some k1 ->
      case k1 of {
       Kind_Base ->
        let {s = iHT (Cons (Pair b k0) _UU0394_0) Kind_Base __} in
        case s of {
         Inl s0 -> Inl
          (case s0 of {
            ExistT x s1 -> ExistT (Ty_Forall b k0 x) (Step_forall b k0 t0 x
             s1)});
         Inr _ -> Inr __};
       Kind_Arrow _ _ -> false_rec};
     None -> false_rec}) (\_ _ _ _ -> Inr __) (\b k0 t0 iHT _UU0394_0 _ _ ->
    let {o = kind_check (Cons (Pair b k0) _UU0394_0) t0} in
    case o of {
     Some k1 ->
      let {s = iHT (Cons (Pair b k0) _UU0394_0) k1 __} in
      case s of {
       Inl s0 -> Inl
        (case s0 of {
          ExistT x s1 -> ExistT (Ty_Lam b k0 x) (Step_abs b k0 t0 x s1)});
       Inr _ -> Inr __};
     None -> false_rec}) (\t1 iHT1 t2 iHT2 _UU0394_0 _ _ ->
    let {o = kind_check _UU0394_0 t1} in
    case o of {
     Some k0 ->
      case k0 of {
       Kind_Base -> false_rec;
       Kind_Arrow k1 k2 ->
        let {o0 = kind_check _UU0394_0 t2} in
        case o0 of {
         Some k3 ->
          let {b = kind_eqb k1 k3} in
          case b of {
           True ->
            let {s = iHT1 _UU0394_0 (Kind_Arrow k1 k2) __} in
            case s of {
             Inl s0 -> Inl
              (case s0 of {
                ExistT x s1 -> ExistT (Ty_App x t2) (Step_appL t1 x t2 s1)});
             Inr _ ->
              let {o1 = kind_check _UU0394_0 t1} in
              case o1 of {
               Some k4 ->
                case k4 of {
                 Kind_Base -> false_rec;
                 Kind_Arrow k5 _ ->
                  let {o2 = kind_check _UU0394_0 t2} in
                  case o2 of {
                   Some k6 ->
                    let {b0 = kind_eqb k5 k6} in
                    case b0 of {
                     True ->
                      let {s0 = iHT2 _UU0394_0 k6 __} in
                      case s0 of {
                       Inl s1 -> Inl
                        (case s1 of {
                          ExistT x s2 -> ExistT (Ty_App t1 x) (Step_appR t1
                           t2 x s2)});
                       Inr _ ->
                        ty_rec (\_ _ _ _ _ _ _ -> Inr __)
                          (\_ _ _ _ _ _ _ _ _ _ -> false_rec)
                          (\_ _ _ _ _ _ _ _ _ _ -> false_rec)
                          (\_ _ _ _ _ _ _ _ _ _ -> false_rec)
                          (\_ _ _ _ _ _ _ -> false_rec)
                          (\b1 k7 t3 _ _ _ _ _ _ _ -> Inl (ExistT
                          (substituteTCA b1 t2 t3) (Step_beta b1 k7 t3 t2)))
                          (\_ _ _ _ _ _ _ _ _ _ -> Inr __) t1 iHT1 __ __ __
                          __ __};
                     False -> false_rec};
                   None -> false_rec}};
               None -> false_rec}};
           False -> false_rec};
         None -> false_rec}};
     None -> false_rec}) t _UU0394_ k __

normaliser_gas :: Nat -> Ty -> (List (Prod BinderTyname Kind)) -> Kind -> Ty
normaliser_gas n t _UU0394_ k =
  case n of {
   O -> t;
   S n' ->
    case step_dec t _UU0394_ k of {
     Inl s -> case s of {
               ExistT t' _ -> normaliser_gas n' t' _UU0394_ k};
     Inr _ -> t}}


data Unit =
   Tt

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

type BinderName = String
type Name = String

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