err Arrow "Missing arrow (<-) after rule name"
err ArrowDash "Missing dash in arrow (<-)"
err Expr "Missing expression for the rule"
err Seq "Missing expression after Choice operator (/)"
err Close "Missing closing parenthesis"
err SingleStr "Missing closing single quote (')"
err DoubleStr "Missing closing double quote (\")"
err Class "Missing closing square bracket (])"

lng LangLangParser {
  Grammar    = Spacing %Definition+ EndOfFile
  Definition = %Identifier LEFTARROW^Arrow Expression^Expr
  Expression <- %Sequence (SLASH %Sequence^Seq)
  Sequence   <- %Prefix*
  Prefix     <- (%AND / %NOT)? %Labeled
  Labeled    <- %Suffix %label?
  Suffix     <- %Primary (%QUESTION / %STAR / %PLUS)?
  Primary    <- %BlockCapture
              / %CAPTURE? %Identifier !LEFTARROW
              / OPEN Expression CLOSE^Close
              / %Literal / %Class / %DOT

  # Lexical syntax
  Identifier <- %{ IdentStart IdentCont* } Spacing
  IdentStart <- [a-zA-Z_]
  IdentCont  <- IdentStart / [0-9]

  Literal    <- ['] (!['] %Char)* [']^SingleStr Spacing
              / ["] (!["] %Char)* ["]^DoubleStr Spacing
  Class      <- '[' (!']' %Range)* ']'^Class Spacing
  Range      <- %Char '-' %Char / %Char
  Char       <- %{ '\\' [nrt'"\[\]\\]^Special }
              / %{ '\\' [0-2][0-7][0-7]^TSS }
              / %{ '\\' [0-7]^Ss[0-7]? }
              ## Hex-chars Extension  
              / %{ '\\x' [0-9a-fA-F]+^Hex }
              / %{ !'\\' .^Char }

  LABEL      <- '^'
  LEFTARROW  <- '<' '-'^ArrowDash Spacing
  SLASH      <- '/' Spacing
  AND        <- '&' Spacing
  NOT        <- '!' Spacing
  QUESTION   <- '?' Spacing
  STAR       <- '*' Spacing
  PLUS       <- '+' Spacing
  OPEN       <- '(' Spacing
  CLOSE      <- ')' Spacing
  DOT        <- '.' Spacing
  ## Extensions
  CAPTURE    <- '%' Spacing
  OPCB       <- '%{' Spacing
  CLCB       <- '}' Spacing

  Spacing    <- (Space / %Comment)*
  Comment    <- '#' %{ (!EndOfLine .)* } EndOfLine
  Space      <- ' ' / '\t' / EndOfLine
  EndOfLine  <- '\r\n' / '\n' / '\r'
  EndOfFile  <- !.
}

LangLangTranslator {
  Grammar({ "Grammar" Definition*:d }) {
     
  }

  Definition <- { "Definition" Identifier Expression }
  Identifier <- { "Identifier" Atom }
  Literal    <- { "Literal" Atom@atom }                      -> position = location()
                                                             -> atom.each(i: emit("char", ord(i)))
                                                             -> location() - position
  Atom       <- !{ .* } .
}
