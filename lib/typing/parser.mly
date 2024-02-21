
%{
open Rethfl_util
open Rethfl_syntax

let map = ref []
let assoc name =
  try
    Stdlib.List.assoc name !map
  with Not_found ->
    let x = Id.gen ~name `Int in
    map := (name,x) :: !map;
    x
%}

%token <int> INT
%token <string> LIDENT
%token <string> UIDENT

%token START_TYPE EOF
%token LPAREN  "(" RPAREN  ")"
%token LSQUARE "[" RSQUARE "]"
%token LANGRE  "<" RANGRE  ">"
%token TRUE "tt" FALSE "ff"
%token COLON ":"

%token PLUS  "+" MINUS "-" STAR  "*" SLASH "/" PERCENT "%" NEG
%token EQ "=" NEQ "<>" LE "<=" GE ">=" /* LT "<" GT ">" */
%token AND "/\\" OR "\\/"

%token TBOOL TINT TARROW "->"

%right OR
%right AND
%left PLUS MINUS
%left STAR
%nonassoc NEG

%type <string * Rtype.t> annot
%start annot


%%

annot:
    | START_TYPE f=uvar ":" ty=ty EOF { f,  ty }

ty:
| ty=refinement_ty { map := []; ty }

refinement_ty:
| "*"                    { RBool(RTrue) }
| "*" "[" predicate "]"  { RBool($3) }
| TINT                   { RInt (RId (Id.gen ~name:"x" `Int)) }
| name=lvar ":" TINT "->" ty=refinement_ty
    { let x = assoc name in
      Rtype.RArrow(RInt(RId x), ty)
    }
| "(" name=lvar ":" TINT ")" "->" ty=refinement_ty
    { let x = assoc name in
      Rtype.RArrow(RInt(RId x), ty)
    }
| ty1=refinement_ty "->" ty2=refinement_ty
    {
      Rtype.RArrow(ty1, ty2)
    }
| "(" ty=refinement_ty ")" { ty }

predicate:
| and_or_predicate { $1 }

and_or_predicate:
| p1=and_or_predicate "/\\" p2=and_or_predicate { RAnd(p1, p2) }
| p1=and_or_predicate "\\/" p2=and_or_predicate { ROr(p1, p2) }
| p=a_predicate                                { p }

a_predicate:
| atom_predicate           { $1 }
| a1=arith p=pred a2=arith { RPred(p, [a1; a2]) }

arith:
| atom_arith          { $1                                  }
| arith op arith      { Arith.mk_op $2  [$1;$3]             }
| "-" arith %prec NEG { Arith.mk_op Sub Arith.[mk_int 0;$2] }

atom_arith:
| "(" arith ")" { $2                        }
| INT           { Arith.mk_int $1           }
| name=lvar     { Arith.mk_var (assoc name) }

atom_predicate:
| TRUE  { RTrue  }
| FALSE { RFalse }
| "(" p=predicate ")" { p }


(******************************************************************************)
(* Util                                                                       *)
(******************************************************************************)

%inline op:
| "+" { Arith.Add  }
| "-" { Arith.Sub  }
| "*" { Arith.Mult }
| "/" { Arith.Div }
| "%" { Arith.Mod }

pred:
| "="  { Formula.Eq  }
| "<>" { Formula.Neq }
| "<=" { Formula.Le  }
| ">=" { Formula.Ge  }
| "<"  { Formula.Lt  }
| ">"  { Formula.Gt  }

lvar:
(* Adhoc way. Because hoice complains the use of _ as an identity *)
| LIDENT { if $1 = "_" then "replaced!" else $1 }

uvar:
| UIDENT { $1 }
