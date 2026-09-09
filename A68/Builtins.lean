import A68.Mode

/-!
# A68.Builtins — modes of the standard prelude

Names are stored without spaces, as produced by the lexer (`new line` → `newline`).
Values of the constants and the semantics of procedures live in `A68.Interp`.
-/
namespace A68.Builtins

open Mode

def INT : Mode := int 0
def REAL : Mode := real 0
def LINT : Mode := int 1
def LREAL : Mode := real 1
def STRING : Mode := Mode.string
def REFFILE : Mode := ref file
def RSIMPLOUT : Mode := row 1 false simplout
def RSIMPLIN : Mode := row 1 false simplin
def PROCFILE : Mode := proc [REFFILE] void

def realFn (n : Int) : Mode := proc [real n] (real n)

/-- Constants (name, mode). -/
def consts : List (String × Mode) :=
  [("maxint", INT), ("minint", INT), ("maxreal", REAL), ("minreal", REAL), ("smallreal", REAL), ("pi", REAL),
   ("longmaxint", LINT), ("longlongmaxint", int 2), ("longmaxreal", LREAL), ("longsmallreal", LREAL),
   ("longlongmaxreal", real 2), ("longlongsmallreal", real 2), ("longpi", LREAL), ("longlongpi", real 2),
   ("intwidth", INT), ("realwidth", INT), ("expwidth", INT),
   ("longintwidth", INT), ("longrealwidth", INT), ("longexpwidth", INT),
   ("longlongintwidth", INT), ("longlongrealwidth", INT), ("longlongexpwidth", INT),
   ("bitswidth", INT), ("longbitswidth", INT), ("byteswidth", INT), ("maxabschar", INT),
   ("intlengths", INT), ("intshorths", INT), ("reallengths", INT), ("realshorths", INT),
   ("bitslengths", INT), ("byteslengths", INT),
   ("nullcharacter", char), ("blank", char), ("flip", char), ("flop", char), ("errorchar", char),
   ("standout", REFFILE), ("standin", REFFILE), ("standerror", REFFILE), ("standback", REFFILE),
   ("standoutchannel", channel), ("standinchannel", channel), ("standbackchannel", channel),
   ("newline", PROCFILE), ("newpage", PROCFILE), ("space", PROCFILE), ("backspace", PROCFILE),
   ("stop", proc [] void), ("random", proc [] REAL), ("longrandom", proc [] LREAL),
   ("clock", proc [] REAL), ("seconds", proc [] REAL), ("cputime", proc [] REAL),
   ("nil", ref void), ("programidf", STRING)]

/-- Procedures (name, mode). -/
def procs : List (String × Mode) :=
  [("print", proc [RSIMPLOUT] void), ("write", proc [RSIMPLOUT] void),
   ("printf", proc [RSIMPLOUT] void), ("writef", proc [RSIMPLOUT] void),
   ("put", proc [REFFILE, RSIMPLOUT] void), ("putf", proc [REFFILE, RSIMPLOUT] void),
   ("read", proc [RSIMPLIN] void), ("readf", proc [RSIMPLIN] void),
   ("get", proc [REFFILE, RSIMPLIN] void), ("getf", proc [REFFILE, RSIMPLIN] void),
   ("whole", proc [number, INT] STRING), ("fixed", proc [number, INT, INT] STRING),
   ("float", proc [number, INT, INT, INT] STRING), ("real", proc [number, INT, INT, INT, INT] STRING),
   ("charinstring", proc [char, ref INT, STRING] bool),
   ("stringinstring", proc [STRING, ref INT, STRING] bool),
   ("lastcharinstring", proc [char, ref INT, STRING] bool),
   ("toupper", proc [char] char), ("tolower", proc [char] char),
   ("isupper", proc [char] bool), ("islower", proc [char] bool), ("isdigit", proc [char] bool),
   ("isalpha", proc [char] bool), ("isalnum", proc [char] bool), ("isspace", proc [char] bool),
   ("ispunct", proc [char] bool), ("isprint", proc [char] bool), ("iscntrl", proc [char] bool),
   ("isgraph", proc [char] bool), ("isxdigit", proc [char] bool),
   ("odd", proc [INT] bool), ("abs", proc [INT] INT),
   ("nextrandom", proc [] REAL), ("firstrandom", proc [INT] void), ("randomint", proc [INT] INT),
   ("sqrt", realFn 0), ("exp", realFn 0), ("ln", realFn 0), ("log", realFn 0),
   ("sin", realFn 0), ("cos", realFn 0), ("tan", realFn 0),
   ("arcsin", realFn 0), ("arccos", realFn 0), ("arctan", realFn 0),
   ("asin", realFn 0), ("acos", realFn 0), ("atan", realFn 0),
   ("sinh", realFn 0), ("cosh", realFn 0), ("tanh", realFn 0),
   ("arcsinh", realFn 0), ("arccosh", realFn 0), ("arctanh", realFn 0),
   ("cbrt", realFn 0), ("curt", realFn 0), ("exp2", realFn 0), ("log2", realFn 0), ("log10", realFn 0),
   ("arctan2", proc [REAL, REAL] REAL), ("atan2", proc [REAL, REAL] REAL),
   ("complexsqrt", proc [compl 0] (compl 0)), ("csqrt", proc [compl 0] (compl 0)),
   ("complexexp", proc [compl 0] (compl 0)), ("cexp", proc [compl 0] (compl 0)),
   ("complexln", proc [compl 0] (compl 0)), ("cln", proc [compl 0] (compl 0)),
   ("complexsin", proc [compl 0] (compl 0)), ("csin", proc [compl 0] (compl 0)),
   ("complexcos", proc [compl 0] (compl 0)), ("ccos", proc [compl 0] (compl 0)),
   ("longsqrt", realFn 1), ("longexp", realFn 1), ("longln", realFn 1), ("longlog", realFn 1),
   ("longsin", realFn 1), ("longcos", realFn 1), ("longtan", realFn 1),
   ("longarcsin", realFn 1), ("longarccos", realFn 1), ("longarctan", realFn 1),
   ("longlongsqrt", realFn 2), ("longlongexp", realFn 2), ("longlongln", realFn 2),
   ("longlongsin", realFn 2), ("longlongcos", realFn 2), ("longlongtan", realFn 2),
   ("longlongarctan", realFn 2), ("longlongarcsin", realFn 2), ("longlongarccos", realFn 2),
   ("longarctan2", proc [LREAL, LREAL] LREAL),
   ("readint", proc [] INT), ("readreal", proc [] REAL), ("readstring", proc [] STRING),
   ("readchar", proc [] char), ("readbool", proc [] bool), ("readlongint", proc [] LINT),
   ("printint", proc [INT] void), ("printreal", proc [REAL] void), ("printstring", proc [STRING] void),
   ("printchar", proc [char] void), ("printbool", proc [bool] void),
   ("open", proc [REFFILE, STRING, channel] INT), ("close", proc [REFFILE] void),
   ("establish", proc [REFFILE, STRING, channel, INT, INT, INT] INT),
   ("create", proc [REFFILE, channel] INT),
   ("associate", proc [REFFILE, ref STRING] void), ("reset", proc [REFFILE] void),
   ("lock", proc [REFFILE] void), ("scratch", proc [REFFILE] void),
   ("onlogicalfileend", proc [REFFILE, proc [REFFILE] bool] void),
   ("onfileend", proc [REFFILE, proc [REFFILE] bool] void),
   ("onlineend", proc [REFFILE, proc [REFFILE] bool] void),
   ("onpageend", proc [REFFILE, proc [REFFILE] bool] void),
   ("onformatend", proc [REFFILE, proc [REFFILE] bool] void),
   ("onvalueerror", proc [REFFILE, proc [REFFILE] bool] void),
   ("onformaterror", proc [REFFILE, proc [REFFILE] bool] void),
   ("ontransputerror", proc [REFFILE, proc [REFFILE] bool] void),
   ("setexitcode", proc [INT] void), ("setexit", proc [INT] void),
   ("system", proc [STRING] INT), ("argc", proc [] INT), ("argv", proc [INT] STRING),
   ("bitspack", proc [row 1 false bool] (bits 0)), ("bytespack", proc [STRING] (bytes 0)),
   ("charnumber", proc [REFFILE] INT), ("linenumber", proc [REFFILE] INT), ("pagenumber", proc [REFFILE] INT),
   ("makeconv", proc [REFFILE] void)]

def lookup (name : String) : Option Mode :=
  (consts.lookup name).orElse fun _ => procs.lookup name

end A68.Builtins
