%{
    open Past (* open Grammar *)
    open Syntax
         %}

(* tokens *)
(* keywords *)
%token EOF TYPEDEF CONSTDEF SPECDEF MACHINEDEF ASSIGN FUNCDECL EVENTDECL LITDECL LET IN FUNCTION ALL
(* arithmetic operators *)
%token PLUS MINUS STAR DIV LT GT LE GE NEQ EQ
(* logic operators *)
%token NOT AND OR TRUE FALSE IMPL IFF FORALL EXISTS PI
(* splitter *)
%token COLON ARROW COMMA BAR SEMICOLON
(* paranthesis *)
%token LSEQPRAN RSEQPRAN LPAR RPAR LEPAR REPAR
(* regex *)
%token ANY EMP EPSILON CTX REPEAT CONCAT
(* type *)
%token INT BOOL SUBTYPING UNIT PRIME
%token <string> IDENT
%token <string> STRING
%token <int> NUMBER

(* start symbol *)
%start <Past.term> prog_eof
%on_error_reduce statement_list
%%

base_nt:
  | PRIME id=IDENT {Nt.Ty_var id}
  | INT {Nt.Ty_int}
  | BOOL {Nt.Ty_bool}
  | UNIT {Nt.Ty_unit}
  | nt1=nt ARROW nt2=nt {Nt.mk_arr nt1 nt2}
  | nt=nt id=IDENT {Nt.Ty_constructor (id, [nt]) }
  | id=IDENT {Nt.Ty_constructor (id, [])}
  | LPAR nt=nt RPAR {nt}
  | LT ts=type_feilds GT {Nt.Ty_record ts}
  | LT ts=type_feilds SEMICOLON GT {Nt.Ty_record ts}
;

type_feilds:
  | id=IDENT COLON nt=base_nt {[(id, nt)]}
  | id=IDENT COLON nt=base_nt SEMICOLON ts=type_feilds {(id, nt) :: ts}
;

product_nt:
  | nt1=base_nt STAR nt2=product_nt {nt1 :: nt2}
  | nt1=base_nt STAR nt2=base_nt {[nt1; nt2]}
;

arr_nt:
  | nt1=base_nt ARROW nt2=arr_nt {Nt.mk_arr nt1 nt2}
  | nt1=base_nt ARROW nt2=base_nt {Nt.mk_arr nt1 nt2}
;

nt:
  | nt=base_nt {nt}
  | nt=arr_nt {nt}
  | nts=product_nt {Nt.mk_tuple nts}
  ;


biop:
| PLUS {"+"}
  | MINUS {"-"}
  | STAR {"*"}
  | DIV {"/"}
  | LT {"<"}
  | GT {">="}
  | LE {">="}
  | GE {">"}
  | EQ {"=="}
  | NEQ {"!="}
;

typed_var:
  | LPAR id=IDENT COLON nt=nt RPAR {id #: (Some nt)}
  | id=IDENT {id #: None}
;

typed_vars:
  | c=typed_var cs=typed_vars {c :: cs}
  | c=typed_var {[c]}
;

vars:
  | c=IDENT cs=vars {c :: cs}
  | c=IDENT {[c]}
  ;

constant:
  | TRUE {B true}
  | FALSE {B false}
  | n=NUMBER {I n}
| LSEQPRAN cs=constant_list RSEQPRAN {SetLiteral cs}
;

  constant_list:
| c=constant SEMICOLON cs=constant_list {c :: cs}
| c=constant {[c]}
;

  lit:
| c=constant {AC c}
| id=typed_var {AVar id}
| l1=typed_lit op=biop l2=typed_lit {AAppOp (op #: (None), [l1; l2])}
| LPAR lit=lit RPAR {lit}
;

  typed_lit:
| LPAR lit=lit COLON nt=nt RPAR {lit #: (Some nt)}
| lit=lit {lit #: (None)}
;

prop:
| p1=prop_base IMPL p2=prop {{y = Implies(p1.y, p2.y); loc = $startpos}}
| p1=prop_base IFF p2=prop {{y = Iff(p1.y, p2.y); loc = $startpos}}
| p1=prop_base OR p2=prop {{y = Or [p1.y; p2.y]; loc = $startpos}}
| p1=prop_base AND p2=prop {{y = And [p1.y; p2.y]; loc = $startpos}}
| p=prop_base {p}
;

prop_base:
| NOT p1=prop {{y = Not(p1.y); loc = $startpos}}
| FORALL qv=typed_var COMMA p=prop {{y = Forall {qv; body = p.y}; loc = $startpos}}
| EXISTS qv=typed_var COMMA p=prop {{y = Exists {qv; body = p.y}; loc = $startpos}}
| l=typed_lit {{y = Lit l; loc = $startpos}}
| LPAR prop=prop RPAR {prop}
;

sevent:
| LEPAR op=IDENT vs=typed_vars BAR p=prop REPAR {{y = normalize_name (EffEvent {op; vs; phi = p.y}); loc = $startpos}}
;

regex_case:
| op=IDENT ARROW p=prop {{y = normalize_name (EffEvent {op; vs = []; phi = p.y}); loc = $startpos}}
| ALL ARROW p=prop {{y = normalize_name (EffEvent {op = "all"; vs = []; phi = p.y}); loc = $startpos}}
;

regex_case_list:
| c=regex_case BAR cs=regex_case_list {c :: cs}
| c=regex_case {[c]}
;

regex_match:
| FUNCTION BAR cs=regex_case_list {{ y = mk_sevents_from_ses (List.map (fun x ->x.y) cs); loc = $startpos}}
| FUNCTION cs=regex_case_list {{ y = mk_sevents_from_ses (List.map (fun x ->x.y) cs); loc = $startpos}}
;

regex_base:
  | EMP {{y = EmptyA; loc = $startpos}}
  | EPSILON {{y = EpsilonA; loc = $startpos}}
  | p1=regex_base CONCAT p2=regex_base {{y = SeqA(p1.y, p2.y); loc = $startpos}}
  | p1=regex_base OR p2=regex_base {{y = LorA(p1.y, p2.y); loc = $startpos}}
  | p1=regex_base AND p2=regex_base {{y = LandA(p1.y, p2.y); loc = $startpos}}
  | REPEAT n=NUMBER p=regex_base {{y = RepeatN (n, p.y); loc = $startpos}}
  | r=regex_base STAR {{y = StarA r.y; loc = $startpos}}
  | s=sevent {{y =Atomic s.y; loc = $startpos}}
  | LEPAR r=regex_match REPAR {{y = r.y; loc = $startpos}}
  | r=regex_extention {{y = Extension r.y; loc = $startpos}}
  | r=regex_sugar {{y = SyntaxSugar r.y; loc = $startpos}}
  | LPAR r=regex RPAR {r}
;

regex_extention:
  | ANY {{y = AnyA; loc = $startpos}}
  | NOT p=regex {{y = ComplementA p.y; loc = $startpos}}
  ;

regex_sugar:
  | p1=regex MINUS p2=regex {{y = SetMinusA(p1.y, p2.y); loc = $startpos}}
  | CTX LSEQPRAN op_names=vars RSEQPRAN p=regex {{y = CtxOp {op_names; body = p.y}; loc = $startpos}}
  ;

regex_expr:
  | FORALL LPAR id=IDENT COLON nt=nt RPAR COMMA p=regex {{y = QFRegex {qv = id #: (RForall nt); body = p.y}; loc = $startpos}}
  | EXISTS LPAR id=IDENT COLON nt=nt RPAR COMMA p=regex {{y = QFRegex {qv = id #: (RExists nt); body = p.y}; loc = $startpos}}
  | PI LPAR qv=IDENT SUBTYPING nt=nt RPAR COMMA p=regex {{y = QFRegex {qv = qv #: (RPi nt); body = p.y}; loc = $startpos}}
  | FORALL LPAR qv=IDENT SUBTYPING nt=nt RPAR COMMA p=regex {{y = QFRegex {qv = qv #: (RPi nt); body = p.y}; loc = $startpos}}
  | regex=regex_base {{y = RRegex regex.y; loc = $startpos}}
  | LET lhs=typed_var ASSIGN rhs=regex_expr IN body=regex {{y = RLet {lhs; rhs = rhs.y; body = body.y}; loc = $startpos}}
  | id=typed_var {{y = RVar id; loc = $startpos}}
  | c=constant {{y = RConst c; loc = $startpos}}
  | es=regex_expr_list {
             match es with
             | f :: args ->
                let y = List.fold_left (fun func arg -> RApp {func = RExpr func; arg = arg.y}) f.y args in
                {y; loc = $startpos}
             | [] -> failwith "die"
         }
  | REPEAT n=IDENT p=regex_base {{y = Repeat (n, p.y); loc = $startpos}}
;

regex_expr_list:
  | c=regex_expr BAR cs=regex_expr_list {c :: cs}
  | c1=regex_expr c2=regex_expr {[c1; c2]}
  ;

regex:
  | r=regex_base {r}
  | r=regex_expr {{y = RExpr r.y; loc = $startpos}}
  ;

statement:
  | TYPEDEF id=IDENT SUBTYPING nt=nt {{y = MTyDeclSub {type_name = id; super_ty = nt}; loc = $startpos}}
  | LITDECL id=IDENT ASSIGN p=prop {{y = MAxiom {name = id; prop = p.y}; loc = $startpos}}
  | FUNCDECL id=IDENT COLON nt=nt {{y = MValDecl (id #: (Some nt)); loc = $startpos}}
  | FUNCDECL id=STRING COLON nt=nt {{y = MValDecl (id #: (Some nt)); loc = $startpos}}
  | EVENTDECL id=IDENT COLON nt=nt {{y = MValDecl (id #: (Some nt)); loc = $startpos}}
  | TYPEDEF id=IDENT ASSIGN c=constant {{y = MRegex {name = (id #: None); automata = RExpr (RConst c)}; loc = $startpos}}
  | CONSTDEF id=IDENT ASSIGN c=constant {{y = MRegex {name = (id #: None); automata = RExpr (RConst c)}; loc = $startpos}}
  | SPECDEF id=IDENT ASSIGN q=regex {{y = MRegex {name = (id #: None); automata = q.y}; loc = $startpos}}
  | MACHINEDEF id=IDENT ASSIGN q=regex {{y = MRegex {name = (id #: None); automata = q.y}; loc = $startpos}}
  ;

statement_list:
  | c=statement SEMICOLON cs=statement_list {c :: cs}
  | c=statement {[c]}
  ;


prog_eof:
  | s=statement_list ; EOF { s }
;
%%
(* statement: *)
(*   | LPAR ITE s1=statement s2=statement s3=statement RPAR {{loc = $startpos; x = Ite (s1, s2, s3)}} *)
(*   | LPAR AND s=statements RPAR {{loc = $startpos; x = And s}} *)
(*   | LPAR OR s=statements RPAR {{loc = $startpos; x = Or s}} *)
(*   | LPAR NOT s=statement RPAR {{loc = $startpos; x = Not s}} *)
(*   | LPAR EQ l1=statement l2=lit RPAR {{loc = $startpos; x = OpEq (l1, l2)}} *)
(*   | LPAR LE l1=lit l2=statement RPAR {{loc = $startpos; x = OpLe (l1, l2)}} *)
(*   | LPAR LET LPAR LPAR lhs=IDENT rhs=statement RPAR RPAR body=statement RPAR {{loc = $startpos; x = Let (lhs, rhs, body)}} *)
(*   | TRUE {{loc = $startpos; x = True}} *)
(*   | FALSE {{loc = $startpos; x = Not {loc = $startpos; x = True}}} *)
(*   | n=IDENT {{loc = $startpos; x = App (n, [])}} *)
(*   | LPAR n=IDENT lits=lits RPAR {{loc = $startpos; x = App (n, lits)}} *)
(*   | lit=lit {{loc = $startpos; x = Lit lit}} *)
(* ; *)

(* lits: *)
(*   | s1=lit s2=lits {s1 :: s2} *)
(*   | s1=lit {[s1]} *)
(* ; *)
(* lit: *)
(*   | LPARVAR n=NUMBER RPAR {VarI n} *)
(*   | n=NUMBER {CI n} *)
(*   | LPAR MINUS n=NUMBER RPAR {CI (- n)} *)
(* ; *)
(* %% *)
