(require 'jezebel-mode)

(jez-define-grammar jez-c-mode-grammar
  (:token "!"
          "!="
          "%="
          "&"
          "&="
          "("
          ")"
          "*"
          "*="
          "+"
          "+="
          ","
          "-"
          "-"
          "."
          "..."
          "/="
          ";"
          "<<"
          "<<="
          "<="
          "=="
          ">="
          ">>"
          ">>="
          "["
          "]"
          "^="
          "auto"
          "break"
          "case"
          "char"
          "const"
          "continue"
          "default"
          "do"
          "double"
          "else"
          "enum"
          "extern"
          "float"
          "for"
          "goto"
          "if"
          "int"
          "long"
          "register"
          "return"
          "short"
          "signed"
          "sizeof"
          "static"
          "struct"
          "switch"
          "typedef"
          "union"
          "unsigned"
          "void"
          "volatile"
          "while"
          "|="
          "~"
          "&&"
          CONSTANT
          "--"
          IDENTIFIER
          "++"
          "||"
          PTR-OP
          STRING-LITERAL
          TYPE-NAME)

  (:start translation-unit)

  (primary-expression
   (/ IDENTIFIER
      CONSTANT
      STRING-LITERAL
      (: "(" expression ")" )))

  (postfix-expression
   (/ (: primary-expression)
      (: postfix-expression "[" expression "]")
      (: postfix-expression "(" ")")
      (: postfix-expression "(" argument-expression-list ")")
      (: postfix-expression "." IDENTIFIER)
      (: postfix-expression PTR-OP IDENTIFIER)
      (: postfix-expression "++")
      (: postfix-expression "--")))

  (argument-expression-list
   (/ (: assignment-expression)
      (: argument-expression-list "," assignment-expression)))

  (unary-expression
   (/ (: postfix-expression)
      (: "++" unary-expression)
      (: "--" unary-expression)
      (: unary-operator cast-expression)
      (: "sizeof" unary-expression)
      (: "sizeof" "(" type-name ")")))

  (unary-operator
   (/ "&" "*" "+" "-" "~" "!"))

  (cast-expression
   (/ (: unary-expression)
      (: "(" type-name ")" cast-expression)))

  (multiplicative-expression
   (/ (: cast-expression)
      (: multiplicative-expression "*" cast-expression)
      (: multiplicative-expression "/" cast-expression)
      (: multiplicative-expression "%" cast-expression)))

  (additive-expression
   (/ (: multiplicative-expression)
      (: additive-expression "+" multiplicative-expression)
      (: additive-expression "-" multiplicative-expression)))

  (shift-expression
   (/ (: additive-expression)
      (: shift-expression "<<" additive-expression)
      (: shift-expression ">>" additive-expression)))

  (relational-expression
   (/ (: shift-expression)
      (: relational-expression "<" shift-expression)
      (: relational-expression ">" shift-expression)
      (: relational-expression "<=" shift-expression)
      (: relational-expression ">=" shift-expression)))

  (equality-expression
   (/ (: relational-expression)
      (: equality-expression "==" relational-expression)
      (: equality-expression "!=" relational-expression)))

  (and-expression
   (/ (: equality-expression)
      (: and-expression "&" equality-expression)))

  (exclusive-or-expression
   (/ (: and-expression)
      (: exclusive-or-expression "^" and-expression)))

  (inclusive-or-expression
   (/ (: exclusive-or-expression)
      (: inclusive-or-expression "|" exclusive-or-expression)))

  (logical-and-expression
   (/ (: inclusive-or-expression)
      (: logical-and-expression "&&" inclusive-or-expression)))

  (logical-or-expression
   (/ (: logical-and-expression)
      (: logical-or-expression "||" logical-and-expression)))

  (conditional-expression
   (/ (: logical-or-expression)
      (: logical-or-expression
         "?" expression
         ":" conditional-expression)))

  (assignment-expression
   (/ (: conditional-expression)
      (: unary-expression assignment-operator assignment-expression)))

  (assignment-operator
   (/ "="
      "*="
      "/="
      "%="
      "+="
      "-="
      "<<="
      ">>="
      "&="
      "^="
      "|="))

  (expression
   (/ (: assignment-expression)
      (: expression "," assignment-expression)))

  (constant-expression
   conditional-expression)

  (declaration
   (/ (: declaration-specifiers ";")
      (: declaration-specifiers init-declarator-list ";")))

  (declaration-specifiers
   (/ (: storage-class-specifier)
      (: storage-class-specifier declaration-specifiers)
      (: type-specifier)
      (: type-specifier declaration-specifiers)
      (: type-qualifier)
      (: type-qualifier declaration-specifiers)))

  (init-declarator-list
   (/ (: init-declarator)
      (: init-declarator-list "," init-declarator)))

  (init-declarator
   (/ (: declarator)
      (: declarator "=" initializer)))

  (storage-class-specifier
   (/ "typedef" "extern" "static" "auto" "register"))

  (type-specifier
   (/ "void" "char" "short" "int" "long" "float" "double" "signed" "unsigned"
      string-or-union-specifier
      enum-specifier
      TYPE-NAME))

  (struct-or-union-specifier
   (/ (: struct-or-union identifier "{" struct-declaration-list "}")
      (: struct-or-union "{" struct-declaration-list "}")
      (: struct-or-union IDENTIFIER)))

  (struct-or-union
   (/ "struct" "union"))

  (struct-declaration
   (specifier-qualifier-list struct-declarator-list ";"))

  (specifier-qualifier-list
   (/ (: type-specifier specifier-qualifier-list)
      (: type-specifier)
      (: type-qualifier specifier-qualifier-list)
      (: type-qualifier)))

  (struct-declarator-list
   (/ (: struct-declarator)
      (: struct-declarator-list "," struct-declarator)))

  (struct-declarator
   (/ (: declarator)
      (: ":" constant-expression)
      (: declarator ":" constant-expression)))

  (enum-specifier
   (/ (: "enum" "{" enumerator-list "}")
      (: "enum" IDENTIFIER "{" enumerator-list "}")
      (: "enum" IDENTIFIER)))

  (enumerator-list
   (/ (: enumerator)
      (: enumerator-list "," enumerator)))

  (enumerator
   (/ (: IDENTIFIER)
      (: IDENTIFIER "+" constant-expression)))

  (type-qualifier
   (/ "const" "volatile"))

  (declarator
   (/ (: pointer direct-declarator)
      (: direct-declarator)))

  (direct-declarator
   (/ (: IDENTIFIER)
      (: "(" declarator ")")
      (: direct-declarator "[" constant-expression "]")
      (: direct-declarator "[" "]")
      (: direct-declarator "(" parameter-type-list ")")
      (: direct-declarator "(" identifier-list ")")
      (: direct-declarator "(" ")")))

  (pointer
   (/ (: "*")
      (: "*" type-qualifier-list)
      (: "*" pointer)
      (: "*" type-qualifier-list pointer)))

  (type-qualifier-list
   (/ (: type-qualifier)
      (: type-qualifier-list type-qualifier)))

  (parameter-type-list
   (/ (: parameter-list)
      (: parameter-list "," "...")))

  (parameter-list
   (/ (: parameter-declaration)
      (: parameter-list "," parameter-declaration)))

  (paramater-declaration
   (/ (: declaration-specifiers declarator)
      (: declaration-specifiers abstract-declarator)
      (: declaration-specifiers)))

  (identifier-list
   (/ (: IDENTIFIER)
      (: identifier-list "," IDENTIFIER)))

  (type-name
   (/ (: specifier-qualifier-list)
      (: specifier-qualifier-list abstract-declarator)))

  (abstract-declarator
   (/ (: pointer)
      (: direct-abstract-declarator)
      (: pointer direct-abstract-declarator)))

  (direct-abstract-declarator
   (/ (: "(" abstract-declarator ")")
      (: "[" "]")
      (: "[" constant-expression "]")
      (: direct-abstract-declarator "[" "]")
      (: direct-abstract-declarator "[" constant-expression "]")
      (: "(" ")")
      (: "(" parameter-type-list ")")
      (: direct-abstract-declarator "(" ")")
      (: direct-abstract-declarator "(" parameter-type-list ")")))

  (initializer
   (/ (: assignment-expression)
      (: "{" initializer-list "}")
      (: "{" initializer-list "," "}")))

  (statement
   (/ (: labeled-statement)
      (: compound-statement)
      (: expression-statement)
      (: selection-statement)
      (: iteration-statement)
      (: jump-statement)))

  (labeled-statement
   (/ (: IDENTIFIER ":" statement)
      (: "case" constant-expression ":" statement)
      (: "default" ":" statement)))

  (compound-statement
   (/ (: "{" "}")
      (: "{" statement-list "}")
      (: "{" declaration-list "}")
      (: "{" declaration-list statement-list "}")))

  (declaration-list
   (/ (: declaration)
      (: declaration-list declaration)))

  (statement-list
   (/ (: statement)
      (: statment-list statement)))

  (expression-statement
   (/ (: ";")
      (: expression ":")))

  (selection-statement
   (/ (: "if" "(" expression ")" statement)
      (: "if" "(" expression ")" statement "else" statement)
      (: "switch" "(" expression ")" statement)))

  (iteration-statement
   (/ (: "while" "(" expression ")" statement)
      (: "do" statement "while" "(" expression ")" ";")
      (: "for" "(" expression-statement expression-statement ")" statement)
      (: "for" "("
         expression-statement
         expression-statement
         expression ")"
         statement)))

  (jump-statement
   (/ (: "goto" IDENTIFIER ";")
      (: "continue" ";")
      (: "break" ";")
      (: "return" ";")
      (: "return" expression ";")))

  (translation-unit
   (/ (: external-declaration)
      (: translation-unit external-declaration)))

  (external-declaration
   (/ (: function-definition)
      (: declaration)))

  (function-definition
   (/ (: declaration-specifiers
         declarator
         declaration-list
         compound-statement)
      (: declaration-specifiers
         declarator
         compound-statement)
      (: declarator
         declaration-list
         compound-statement)
      (: declarator compound-statement))))

(provide 'jez-c-mode)
