From MetaCoq.Template Require Import
  TermEquality
  utils
  monad_utils
  Checker
  All
  Pretty
  .

    (*
From PlutusCert Require Import
  Pretty
.
  *)

From Coq Require Import
  Strings.String
  Ascii.

#[local] Open Scope string_scope.

Definition enclose l r s := l ++ s ++ r.

Definition newline := "
".

(* Escape special LaTeX characters *)
Definition escape s :=
  let replace (c : ascii) :=
    if Ascii.eqb c "_"
      then "\_"
      else string_of_list_ascii [c]
  in
  concat "" (map replace (list_ascii_of_string s))
.


Definition latex_command (cmd : string) (opt_args : list string) (args : list string) :=
  concat "" (
    [ "\" ; cmd ]
    ++ map (enclose "[" "]") opt_args
    ++ map (enclose "{" "}") args
    )
.

Definition latex_simple_command cmd arg := latex_command cmd [] [arg].


Definition mathmode str := concat newline
  [ "\["
  ; str
  ; "\]"
  ]
.

Definition linebreak := latex_command "\" [] [].
Definition texttt := latex_simple_command "texttt".
Definition infer (n : nat) rule_name str := latex_command ("infer" ++ string_of_nat n) [rule_name] [str].
Definition hypo := latex_simple_command "hypo".
Definition env env_name body := latex_simple_command "begin" env_name ++ newline ++ body ++ newline ++ latex_simple_command "end" env_name.
Definition documentclass c := latex_simple_command "documentclass" c.
Definition usepackage pkg opt_args := latex_command "usepackage" opt_args [pkg].
Definition vspace h := latex_simple_command "vspace" h.

Definition inferrule name hypos conc := latex_command "inferrule*" ["Right=" ++ name] [concat (" " ++ linebreak ++ newline) hypos; conc].

Definition quote_ind {A} (t : A) : TemplateMonad (global_env_ext × inductive) :=
  '(Σ, ty_closed) <- tmQuoteRec t ;;
  match ty_closed with
    | tInd ind _ => ret (empty_ext Σ, ind)
    | _ => tmFail "Not an inductive type"
  end
    .

Definition rule := string * list (context * aname * term * bool) * (context * term).

Require Import Lists.List.

(* TODO: improve, only should contain free vars from other constructor arguments
, for example not type parameters, or names of inductives in the mindb *)
Fixpoint has_free_vars k t : bool :=
match t with
  | tRel n => k <=? n
  | tProd n s t => has_free_vars k s || has_free_vars (k + 1) t
  | tApp s ts => has_free_vars k s || existsb (has_free_vars k) ts
  | _ => false (* TODO *)
end.


(*
  Consider terms of the form

    (x1 : t_1) -> ... -> t_n

  Returns all the argument types and return type in their respective contexts
*)
Fixpoint ty_params Γ (t : term) : list (context * aname * term * bool) * (context * term) :=
  match t with
    | tProd x σ τ =>
        let decl := mkdecl x None σ in
        let '(args, res) := ty_params (decl :: Γ) τ in
        ((Γ, x, σ, has_free_vars 0 σ) :: args, res)
    | t => ([], (Γ, t))
  end.

(* Constructing rules *)

(* Constructor to rule *)
Definition ctor_to_rule mindb ind (ctor : ident * term * nat) : rule :=
  match ctor with
    | (name , ty , _) =>
        let ty' := type_of_constructor mindb ctor (ind, 0) [] in
        let '(args, r) := ty_params [] ty'
        in (name, args, r)
  end.

(* Inductive to rules *)
Definition ind_rules mindb ind (indb : one_inductive_body) : list rule :=
  map (ctor_to_rule ind mindb) (ind_ctors indb).

(* Mutual inductive to rules *)
Definition mind_rules ind (mindb : mutual_inductive_body) : list (list rule) :=
  map (ind_rules ind mindb) (ind_bodies mindb).

Definition print_var n Γ : option string :=
  match nth_error n Γ with
    | None => None
    | Some (mkdecl (mkBindAnn (nNamed str) _) _ _) => Some str
    | _ => Some "_"
  end.

    (*
Fixpoint print_term (Σ : global_env) Γ (useParens : bool) (t : term) :=
  match t with
    | tRel n =>
      match print_var Γ n with
        | Some str => str
        | None => "<unbound variable: " ++ string_of_nat n ++ " with length Γ = " ++ string_of_nat (List.length Γ ) ++">"
      end
    | tApp t ts =>    enclose "(" ")" (print_term Σ Γ true t)
                   ++ " "
                   ++ concat " " (map (enclose "(" ")"  ∘ print_term Σ Γ true) ts)
    | _ => ""
  end.
    *)
Open Scope string.

Notation test := "test".

Eval cbv in (<% @eq %>).

Definition eq_t (t t' : term) := @eq_term config.default_checker_flags init_graph t t'.

Definition f : term -> string :=
  fun t => match eq_t t <% @eq %> with
    | true => "yes"
    | fals => "no"
  end.

Eval cbv in (f <% @nat %>).


MetaCoq Test Quote (list).


Notation natPat := (tApp
   (tInd
      {|
        inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "list");
        inductive_ind := 0
      |} [])
   [tInd
      {|
        inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
        inductive_ind := 0
      |} []])
.

Notation listPat := <% list %>.

Fail Definition g : term -> string :=
  fun t => match t with
    | listPat => "yes"
    | _ => "no"
  end.


Definition apply_notation (t : term) (args : list string) table : option string :=
  match find (fun '(t', _) => eq_t t t') table with
    | Some (_, f) => f args
    | None => None
  end.

Definition rename renamings x :=
  match find (fun '(y, z) => eq_string x y) renamings with
    | Some (_, y) => y
    | None => x
  end
.

    (*
Definition print_custom Σ Γ (top : bool) table : term -> string :=
  fun t => let fallback := texttt (print_term Σ Γ top t)
  in match t with
    | tApp x args => 
      match lookup x (map (fun t => texttt (print_term Σ Γ false t)) args) table with
        | Some str => str
        | None => fallback
      end
    | _ => fallback
  end.
    *)
Section PP.

Context (renamings : list (string * string)).
Context (notations : list (term × (list string -> option string))).
Context (Σ : global_env_ext).

(*
Definition print_custom Σ Γ (top : bool) table : term -> string :=
  fun t => let fallback := texttt (print_term Σ Γ top t)
  in match t with
    | tApp x args => 
      match lookup x (map (fun t => texttt (print_term Σ Γ false t)) args) table with
        | Some str => str
        | None => fallback
      end
    | _ => fallback
  end.
*)

Fixpoint pp_term Γ (top : bool) (t : term) :=
 match t with
  | tRel n =>
      match nth_error Γ n with
      | Some {| decl_name := na |} =>
          match binder_name na with
          | nAnon => "Anonymous (" ++ string_of_nat n ++ ")"
          | nNamed id => rename renamings id
          end
      | None => "UnboundRel(" ++ string_of_nat n ++ ")"
      end
  | tVar n => "Var(" ++ n ++ ")"
  | tEvar ev _ => "Evar(" ++ string_of_nat ev ++ "[]" ++ ")"
  | tSort s => string_of_sort s
  | tCast c _ t0 =>
      parens top (pp_term Γ true c ++ ":" ++ pp_term Γ true t0)
  | tProd na dom codom =>
      let na' := fresh_name Σ Γ (binder_name na) dom in
      let ann_na' :=
        {| binder_name := na'; binder_relevance := binder_relevance na |} in
      parens top
        ("∀ " ++
         rename renamings (string_of_name na') ++
         " : " ++
         pp_term Γ true dom ++
         ", " ++ pp_term (vass ann_na' dom :: Γ) true codom)
  | tLambda na dom body =>
      let na' := fresh_name Σ Γ (binder_name na) dom in
      let ann_na' :=
        {| binder_name := na'; binder_relevance := binder_relevance na |} in
      parens top
        ("fun " ++
         string_of_name na' ++
         " : " ++
         pp_term Γ true dom ++
         " => " ++ pp_term (vass ann_na' dom :: Γ) true body)
  | tLetIn na def dom body =>
      let na' := fresh_name Σ Γ (binder_name na) dom in
      let ann_na' :=
        {| binder_name := na'; binder_relevance := binder_relevance na |} in
      parens top
        ("let" ++
         string_of_name na' ++
         " : " ++
         pp_term Γ true dom ++
         " := " ++
         pp_term Γ true def ++
         " in " ++ nl ++ pp_term (vdef ann_na' def dom :: Γ) true body)
  | tApp f l =>
      (let printed_args := map (pp_term Γ false) l in
      match apply_notation f printed_args notations with
        | Some str => str
        | None => parens top (pp_term Γ false f ++ "\ " ++ print_list (pp_term Γ false) "\ " l)
      end)
  | tConst c u => texttt (string_of_kername c) ++ print_universe_instance u
  | tInd {| inductive_mind := i; inductive_ind := k |} u =>
      match lookup_ind_decl Σ i k with
      | Some oib => ind_name oib ++ print_universe_instance u
      | None =>
          "UnboundInd(" ++
          string_of_inductive {| inductive_mind := i; inductive_ind := k |} ++
          "," ++ string_of_universe_instance u ++ ")"
      end
  | tConstruct ({| inductive_mind := i; inductive_ind := k |} as ind) l u =>
      match lookup_ind_decl Σ i k with
      | Some oib =>
          match nth_error (ind_ctors oib) l with
          | Some (na, _, _) => na ++ print_universe_instance u
          | None =>
              "UnboundConstruct(" ++
              string_of_inductive ind ++
              "," ++
              string_of_nat l ++ "," ++ string_of_universe_instance u ++ ")"
          end
      | None =>
          "UnboundConstruct(" ++
          string_of_inductive ind ++
          "," ++
          string_of_nat l ++ "," ++ string_of_universe_instance u ++ ")"
      end
  | tCase ({| inductive_mind := mind; inductive_ind := i |} as ind, _, _) p
    t0 brs =>
      match lookup_ind_decl Σ mind i with
      | Some oib =>
          match p with
          | tLambda na _ b =>
              let
                fix print_branch
                  (Γ0 : context) (arity : nat) (br : term) {struct br} :
                    string :=
                  match arity with
                  | 0 => "=> " ++ pp_term Γ0 true br
                  | S n =>
                      match br with
                      | tLambda na0 A B =>
                          let na' := fresh_name Σ Γ0 (binder_name na0) A in
                          let ann_na' :=
                            {|
                              binder_name := na';
                              binder_relevance := binder_relevance na0
                            |} in
                          string_of_name na' ++
                          "  " ++ print_branch (vass ann_na' A :: Γ0) n B
                      | _ => "=> " ++ pp_term Γ0 true br
                      end
                  end in
              let brs0 :=
                map (fun '(arity, br) => print_branch Γ arity br) brs in
              let brs1 := combine brs0 (ind_ctors oib) in
              parens top
                ("match " ++
                 pp_term Γ true t0 ++
                 " as " ++
                 string_of_name (binder_name na) ++
                 " in " ++
                 ind_name oib ++
                 " return " ++
                 pp_term Γ true b ++
                 " with " ++
                 nl ++
                 print_list (fun '(b0, (na0, _, _)) => na0 ++ " " ++ b0)
                   (nl ++ " | ") brs1 ++ nl ++ "end" ++ nl)
          | _ =>
              "Case(" ++
              string_of_inductive ind ++
              "," ++
              string_of_nat i ++
              "," ++
              string_of_term t0 ++
              "," ++
              string_of_term p ++
              "," ++
              string_of_list (fun b : nat × term => string_of_term b.2) brs ++
              ")"
          end
      | None =>
          "Case(" ++
          string_of_inductive ind ++
          "," ++
          string_of_nat i ++
          "," ++
          string_of_term t0 ++
          "," ++
          string_of_term p ++
          "," ++
          string_of_list (fun b : nat × term => string_of_term b.2) brs ++
          ")"
      end
  | tProj ({| inductive_mind := mind; inductive_ind := i |} as ind, _, k) c =>
      match lookup_ind_decl Σ mind i with
      | Some oib =>
          match nth_error (ind_projs oib) k with
          | Some (na, _) => pp_term Γ false c ++ ".(" ++ na ++ ")"
          | None =>
              "UnboundProj(" ++
              string_of_inductive ind ++
              "," ++
              string_of_nat i ++
              "," ++ string_of_nat k ++ "," ++ pp_term Γ true c ++ ")"
          end
      | None =>
          "UnboundProj(" ++
          string_of_inductive ind ++
          "," ++
          string_of_nat i ++
          "," ++ string_of_nat k ++ "," ++ pp_term Γ true c ++ ")"
      end
  | tFix l n =>
      parens top
        ("let fix " ++
         print_defs pp_term Γ l ++
         nl ++
         " in " ++
         nth_default (string_of_nat n)
           (map (string_of_name ∘ binder_name ∘ dname) l) n)
  | tCoFix l n =>
      parens top
        ("let cofix " ++
         print_defs pp_term Γ l ++
         nl ++
         " in " ++
         nth_default (string_of_nat n)
           (map (string_of_name ∘ binder_name ∘ dname) l) n)
  | tInt i => "Int(" ++ string_of_prim_int i ++ ")"
  | tFloat f => "Float(" ++ string_of_float f ++ ")"
  end
.

End PP.

Definition print_hypo renamings table Σ '(Γ, binder, t) : string :=
  let binder_str := match binder with
    | mkBindAnn (nNamed x) rel => texttt x ++ " : "
    | mkBindAnn _ _ => ""
  end in
  binder_str ++ pp_term renamings table Σ Γ true t
.

Definition print_conclusion renamings table Σ '(Γ, t) : string :=
  (pp_term renamings table Σ Γ true t).


Definition sep := (newline ++ vspace "2em" ++ newline).

(* Printing rules *)
Definition print_rule renamings table Σ (r : rule) : string :=
  match r with
    | (name , premises, conclusion) =>
        let depPremises := map fst (filter (fun '(_, b) => b) premises) in
        mathmode
          (inferrule name
            (map (print_hypo renamings table Σ) depPremises)
            (print_conclusion renamings table Σ conclusion)
          )
   end
.
(*
  match r with
    (name , premises, conclusion) => env "prooftree"
      ( concat sep
        (map (print_hypo Σ) premises
        ++ [print_conclusion Σ (List.length premises) name conclusion]
        )
      )
  end
*)
Require Import Strings.String.
Definition pp_rules renamings table ind Σ (mindb : mutual_inductive_body) : string :=
  let print rs := concat (newline ) (map (print_rule renamings table Σ) rs) in
  let all_rules := concat (newline ++ newline) (map print (mind_rules ind mindb)) in

  escape (concat newline
    [ documentclass "article"
    ; usepackage "inputenc" ["utf8x"]
    ; usepackage "textgreek" []
    ; usepackage "mathpartir" []
    ; usepackage "geometry" ["landscape"]
    ; env "document" (enclose newline newline all_rules)
    ])
.

(* Strict version of tmPrint *)
Definition tmPrint' {A} : A -> TemplateMonad unit := fun t => tmEval cbv t >>= tmPrint.

Polymorphic Definition from_option {a} : string -> option a -> TemplateMonad a :=
fun err o => match o with
  | Some x => tmReturn x
  | None   => tmFail err
  end.

Definition print_rules {a : Type} renamings table (t : a) : TemplateMonad unit :=
  '(Σ, ind) <- quote_ind t ;;
  let ind_kname := inductive_mind ind in
  mindb <- from_option "inductive not in Σ" (lookup_minductive (fst Σ) ind_kname) ;;
  tmMsg (pp_rules renamings table ind Σ mindb)
  .

    (*
Inductive expr : nat -> Prop :=
  | Var : string -> expr 0
  | Const : forall n, expr n
  | Plus : forall n m, expr n -> expr m -> expr (n + m)
  .
    *)

Require Import Lists.List.

Inductive ty :=
  | t_var : ty
  | t_fun : ty -> ty -> ty
  .

Inductive expr :=
  | e_var : string -> expr
  | e_app : expr -> expr -> expr
  | e_lam : string -> ty -> expr -> expr
  .

Definition lookup {A} str (env : list (string * A)) :=
  match find (fun '(x, _) => eq_string x str) env with
    | Some (_, y) => Some y
    | None => None
  end.

Inductive has_type : list (string * ty) -> expr -> ty -> Prop :=
  | ty_var : forall env x ty, lookup x env = Some ty -> has_type env (e_var x) ty
  | ty_app : forall env s t ty1 ty2,
      has_type env s (t_fun ty1 ty2) ->
      has_type env t ty1 ->
      has_type env (e_app s t) ty2
  | ty_lam : forall x env ty1 ty2 t,
      has_type ((x, ty1) :: env) t ty2 ->
      has_type env (e_lam x ty1 t) (t_fun ty1 ty2)
  .

Open Scope string.

Definition binop str := 
  fun ts => match ts with
      | [l; r] => Some (l ++ enclose " " " " str ++ r)
      | _ => None
      end.

Definition binop_poly str :=
  fun ts => match ts with
      | [_; l; r] => Some (l ++ enclose " " " " str ++ r)
      | _ => None
      end.

Definition two (f : string -> string -> string) :=
  fun ts => match ts with
      | [l; r] => Some (f l r)
      | _ => None
      end.

Definition three (f : string -> string -> string -> string) :=
  fun ts => match ts with
      | [l; r; x] => Some (f l r x)
      | _ => None
      end.

Definition one (f : string -> string) :=
  fun ts => match ts with
      | [x] => Some (f x)
      | _ => None
      end.

Definition four (f : string -> string -> string -> string -> string) :=
  fun ts => match ts with
      | [x; y; z; w] => Some (f x y z w)
      | _ => None
      end.

Definition renamings :=
  [ ("env", "\Gamma")
  ; ("ty" , "\tau")
  ; ("ty1", "\sigma")
  ; ("ty2", "\tau")
  ]
.

Notation " x '==>' y " := (( <% x %>, y)) (at level 60).

Definition notations :=
  [ t_fun ==> binop "\to"
  ; t_var ==> one id

  ; e_app ==> binop "\ "
  ; e_lam ==> three (fun x ty t =>
        "\lambda " ++
        enclose "(" ")" (x ++ " : " ++ ty) ++
        ".\ " ++ t)
  ; e_var ==> one (fun x => x)

  ; @eq   ==> binop_poly "="

  ; has_type ==> three (fun env t ty => env ++ " \vdash " ++ t ++ " : " ++ ty)

  ; @Some ==>
      two (fun ty x => texttt "Some" ++ "\ " ++ x)

  ; @lookup ==> three (fun A x xs => xs ++ enclose "(" ")" x)
  ; @cons ==> binop_poly ","
  ; @pair ==> four (fun A B x y => enclose "(" ")" (x ++ " : " ++ y))
  ].
MetaCoq Run (print_rules renamings notations has_type).
MetaCoq Run (quote_ind has_type >>= tmPrint).

