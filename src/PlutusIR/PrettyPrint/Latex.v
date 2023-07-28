From MetaCoq.Template Require Import
  TermEquality
  utils
  monad_utils
  Checker
  All.

From PlutusCert Require Import
  Pretty
.

From Coq Require Import
  Strings.String
  Ascii.

#[local] Open Scope string_scope.

Definition enclose l r s := l ++ s ++ r.

Definition newline := "
".

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

Definition quote_ind {A} (t : A) :=
  '(Σ, ty_closed) <- tmQuoteRec t ;;
  match ty_closed with
    | tInd ind _ => ret (TemplateEnvironment.empty_ext Σ, ind)
    | _ => tmFail "Not an inductive type"
  end
    .

Definition rule := string * list (context * aname * term) * (context * term).
Fixpoint ty_params Γ (t : term) : list (context * aname * term) * (context * term) :=
  match t with
    | tProd x σ τ =>
        let decl := mkdecl x None σ in
        let '(args, res) := ty_params (decl :: Γ) τ in
        ((Γ, x, σ) :: args, res)
    | t => ([], (Γ, t))
  end.

(* Constructing rules *)
Definition ctor_to_rule mindb ind (ctor : ident * term * nat) : rule :=
  match ctor with
    | (name , ty , _) =>
        let ty' := type_of_constructor mindb ctor (ind, 0) [] in
        let '(args, r) := ty_params [] ty' in (name, args, r)
  end.

Definition ind_rules mindb ind (indb : one_inductive_body) : list rule :=
  map (ctor_to_rule ind mindb) (ind_ctors indb).

Definition mind_rules ind (mindb : mutual_inductive_body) : list (list rule) :=
  map (ind_rules ind mindb) (ind_bodies mindb).

Definition print_hypo Σ '(Γ, binder, t) : string :=
  let binder_str := match binder with
    | mkBindAnn (nNamed x) rel => texttt x ++ " : "
    | mkBindAnn _ _ => ""
  end in
  binder_str ++ texttt (Pretty.print_term Σ Γ true t)
.

Definition print_conclusion Σ '(Γ, t) : string :=
  texttt (Pretty.print_term Σ Γ true t).


Definition sep := (newline ++ vspace "2em" ++ newline).

(* Printing rules *)
Definition print_rule Σ (r : rule) : string :=
  match r with
    | (name , premises, conclusion) => mathmode
      (inferrule name (map (print_hypo Σ) premises) (print_conclusion Σ conclusion))
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

Definition print_rules ind Σ (mindb : mutual_inductive_body) : string :=
  let print rs := concat (newline ) (map (print_rule Σ) rs) in
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

Definition run_print_rules {a : Type} (t : a) : TemplateMonad unit :=
  '(Σ, ind) <- quote_ind t ;;
  let ind_kname := inductive_mind ind in
  mindb <- from_option "inductive not in Σ" (lookup_minductive (fst Σ) ind_kname) ;;
  tmMsg (print_rules ind Σ mindb)
  .

Inductive expr : nat -> Prop :=
  | Var : string -> expr 0
  | Const : forall n, expr n
  | Plus : forall n m, expr n -> expr m -> expr (n + m)
  .

MetaCoq Run (run_print_rules expr).
