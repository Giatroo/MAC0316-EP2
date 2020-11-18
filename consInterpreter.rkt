#lang plai-typed


; Basic expressions
(define-type ExprC
  [numC     (n : number)]
  [idC      (s : symbol)]
  [plusC    (l : ExprC) (r : ExprC)]
  [multC    (l : ExprC) (r : ExprC)]
  [lamC     (arg : symbol) (body : ExprC)]
  [appC     (fun : ExprC) (arg : ExprC)]
  [ifC      (c : ExprC) (y : ExprC) (n : ExprC)]
  [seqC     (e1 : ExprC) (e2 : ExprC)]
  [equal?C  (e1 : ExprC) (e2 : ExprC)]
  [letC     (name : symbol) (arg : ExprC) (body : ExprC)]
  [let*C    (name1 : symbol) (arg1 : ExprC) (name2 : symbol) (arg2 : ExprC) (body : ExprC)]
  [letrecC  (name : symbol) (arg : ExprC) (body : ExprC)]
  [boolC    (b : boolean)]
  [consC    (car : ExprC) (cdr : ExprC)]
  [carC     (cell : ExprC) ]
  [cdrC     (cell : ExprC)]
  [displayC (exp : ExprC)]
  [quoteC   (sym : symbol)]
  [nullC  ]
  )


; Sugared expressions
(define-type ExprS
  [numS     (n : number)]
  [boolS    (b : boolean)]
  [idS      (s : symbol)]
  [lamS     (arg : symbol) (body : ExprS)]
  [appS     (fun : ExprS) (arg : ExprS)]
  [plusS    (l : ExprS) (r : ExprS)]
  [bminusS  (l : ExprS) (r : ExprS)]
  [uminusS  (e : ExprS)]
  [multS    (l : ExprS) (r : ExprS)]
  [ifS      (c : ExprS) (y : ExprS) (n : ExprS)]
  [seqS     (e1 : ExprS) (e2 : ExprS)]
  [letS     (name : symbol) (arg : ExprS) (body : ExprS)]
  [let*S    (name1 : symbol) (arg1 : ExprS) (name2 : symbol) (arg2 : ExprS) (body : ExprS)]
  [letrecS  (name : symbol) (arg : ExprS) (body : ExprS)]
  [equal?S  (e1 : ExprS) (e2 : ExprS)]
  [consS    (car : ExprS) (cdr : ExprS)]
  [carS     (cell : ExprS) ]
  [cdrS     (cell : ExprS)]
  [displayS (exp : ExprS)]
  [quoteS   (sym : symbol)]
  [nullS ]
)


; Removing the sugar
(define (desugar [as : ExprS]) : ExprC
  (type-case ExprS as
    [numS     (n)        (numC n)]
    [boolS    (b)        (boolC b)]
    [idS      (s)        (idC s)]
    [lamS     (a b)      (lamC a (desugar b))]
    [appS     (fun arg)  (appC (desugar fun) (desugar arg))]
    [plusS    (l r)      (plusC (desugar l) (desugar r))]
    [multS    (l r)      (multC (desugar l) (desugar r))]
    [bminusS  (l r)      (plusC (desugar l) (multC (numC -1) (desugar r)))]
    [uminusS  (e)        (multC (numC -1) (desugar e))]
    [ifS      (c s n)    (ifC (desugar c) (desugar s) (desugar n))]
    [seqS     (e1 e2)    (seqC (desugar e1) (desugar e2))]
    [letS     (n a b)    (letC n (desugar a) (desugar b))]
    [let*S    (n1 a1 n2 a2 b) (let*C n1 (desugar a1) n2 (desugar a2) (desugar b))]
    [letrecS  (n a b)    (letC n (desugar a) (desugar b))]
    [equal?S  (e1 e2)    (equal?C (desugar e1) (desugar e2))]
    [consS    (car cdr) (consC (desugar car) (desugar cdr))]
    [carS     (exp)     (carC (desugar  exp)) ]
    [cdrS     (exp)     (cdrC (desugar  exp)) ]
    [displayS (exp)    (displayC (desugar exp))]
    [quoteS   (sym) (quoteC sym)]
    [nullS    () (nullC)]
    ))


; We need a new value for the box
(define-type Value
  [numV  (n : number)]
  [boolV (b : boolean)]
  [nullV ]
  [quoteV (symb : symbol)]
  [closV (arg : symbol) (body : ExprC) (env : Env)]
  [cellV (first : Value) (second : Value)]
  [suspendV (body : ExprC) (env : Env)]
  )


; Bindings associate symbol with location
(define-type Binding
        [bind (name : symbol) (val : (boxof Value))])

; Env remains the same, we only change the Binding
(define-type-alias Env (listof Binding))
(define mt-env empty)
(define extend-env cons)


; Find the name of a variable
(define (lookup [for : symbol] [env : Env]) : (boxof Value)
       (cond
            [(empty? env) (error 'lookup (string-append (symbol->string for) " was not found"))] ; variable is undefined
            [else (cond
                  [(symbol=? for (bind-name (first env)))   ; found it!
                                 (bind-val (first env))]
                  [else (lookup for (rest env))])]))        ; check in the rest


; Auxiliary operators
(define (num+ [l : Value] [r : Value]) : Value
    (cond
        [(and (numV? l) (numV? r))
             (numV (+ (numV-n l) (numV-n r)))]
        [else
             (error 'num+ "One of the arguments is not a number")]))

(define (num* [l : Value] [r : Value]) : Value
    (cond
        [(and (numV? l) (numV? r))
             (numV (* (numV-n l) (numV-n r)))]
        [else
             (error 'num* "One of the arguments is not a number")]))

(define (strict [v : Value]) : Value
  (type-case Value v
    [numV     (n) v]
    [boolV    (b) v]
    [nullV    ()  v]
    [quoteV   (s) v]
    [closV    (a b e) v]
    [cellV    (f s) v]
    [suspendV (b e) (strict (interp b e))]
  )
)

; Interpreter
(define (interp [a : ExprC] [env : Env]) : Value
  (type-case ExprC a
    ; Numbers just evaluta to their equivalent Value
    [numC (n) (numV n)]

    [boolC (b) (boolV b)]

    ; IDs are retrieved from the Env and unboxed
    [idC (n) (unbox (lookup n env))]

    ; Lambdas evaluate to closures, which save the environment
    [lamC (a b) (closV a b env)]

    ; Application of function
    [appC (f a)
          (local ([define f-value (strict (interp f env))])
            (interp (closV-body f-value)
                    (extend-env
                        (bind (closV-arg f-value) (box (suspendV a env)))
                        (closV-env f-value)
                    )))]

    ; Sum two numbers using auxiliary function
    [plusC (l r) (num+ (strict (interp l env)) (strict (interp r env)))]

    ; Multiplies two numbers using auxiliary function
    [multC (l r) (num* (strict (interp l env)) (strict (interp r env)))]

    ; Conditional operator
    [ifC (c s n) (if (zero? (numV-n (strict (interp c env)))) (interp n env) (interp s env))]

    ; Sequence of operations
    [seqC (b1 b2) (begin (interp b1 env) (interp b2 env))] ; No side effect between expressions!

    ; Declaration of variable
    [letC (name arg body)
          (let* ([new-bind (bind name (box (suspendV arg env)))]
                 [new-env (extend-env new-bind env)])
            (strict (interp body new-env)))]

    [let*C (name1 arg1 name2 arg2 body) (numV 2)]

    [letrecC (name arg body) (numV 2)]

    [equal?C (e1 e2) (boolV (equal? (strict (interp e1 env)) (strict (interp e2 env))))]

    ; Cell operations
    [consC (car cdr)
           (cellV (interp car env) (interp cdr env))]
    [carC  (exp) (cellV-first (interp exp env))]
    [cdrC  (exp) (cellV-second (interp exp env))]
    ;Display values
    [displayC (exp) (let ((value (interp exp env)))
                      (begin (print-value (interp exp env))
                             (display ";") ; no newline in plai-typed, we use ";"
                             value))]
    ;Symbol
    [quoteC (sym) (quoteV sym)]
    ;Null
    [nullC  () (nullV)]

    )
  )


; Parser
(define (parse [s : s-expression]) : ExprS
  (cond
    [(s-exp-number? s) (numS (s-exp->number s))]
    [(s-exp-symbol? s) (idS (s-exp->symbol s))]
    [(s-exp-list? s)
     (let ([sl (s-exp->list s)])
       (if (empty? sl)
           (nullS)
           (case (s-exp->symbol (first sl))
             [(+) (plusS (parse (second sl)) (parse (third sl)))]
             [(*) (multS (parse (second sl)) (parse (third sl)))]
             [(-) (bminusS (parse (second sl)) (parse (third sl)))]
             [(~) (uminusS (parse (second sl)))]
             [(lambda) (lamS (s-exp->symbol (second sl)) (parse (third sl)))] ; definição
             [(call) (appS (parse (second sl)) (parse (third sl)))]
             [(if) (ifS (parse (second sl)) (parse (third sl)) (parse (fourth sl)))]
             [(seq) (seqS (parse (second sl)) (parse (third sl)))]

             [(let) (letS (s-exp->symbol (first (s-exp->list (first (s-exp->list (second sl))))))
                          (parse (second (s-exp->list (first (s-exp->list (second sl))))))
                          (parse (third sl)))]

             [(let*) (let*S
                ; name1
                (s-exp->symbol (first (s-exp->list (first (s-exp->list (second sl))))))
                ; arg1
                (parse (second (s-exp->list (first (s-exp->list (second sl))))))
                ; name2
                (s-exp->symbol (first (s-exp->list (second (s-exp->list (second sl))))))
                ; arg2
                (parse (second (s-exp->list (second (s-exp->list (second sl))))))
                ; body
                (parse (third sl)))]
             [(letrec) (letrecS (s-exp->symbol (first (s-exp->list (first (s-exp->list (second sl))))))
                          (parse (second (s-exp->list (first (s-exp->list (second sl))))))
                          (parse (third sl)))]


             [(cons) (consS (parse (second sl)) (parse (third sl)))]
             [(car) (carS (parse (second sl)))]
             [(cdr) (cdrS (parse (second sl)))]
             [(display)(displayS (parse (second sl)))]
             [(quote) (quoteS (s-exp->symbol (second sl)))]
             [(equal?) (equal?S (parse (second sl)) (parse (third sl)))]
             [else (error 'parse "invalid list input")])))]
    [else (error 'parse "invalid input")]))


; Facilitator
(define (interpS [s : s-expression]) (interp (desugar (parse s)) mt-env))

; Printing
(define (print-value [value : Value ] ) : void
    (type-case Value value
      [numV   (n)     (display n)]
      [boolV  (b)    (display b)]
      [quoteV (symb) (display symb)]
      [closV  (arg body env)
             (begin (display "<<")
                    (display "lambda(")
                    (display arg)
                    (display ")")
                    (display body)
                    (display ";")
                    (display env)
                    (display ">>"))
             ]
      [cellV (first second)
             (begin (display "(")
                    (print-list value)
                    (display ")")
                    )
             ]
      [nullV () (display '())]
      [suspendV (b e) (display "suspV")]
   )
)

(define (print-list cell) : void
  (begin
         (print-value (cellV-first cell))
         (display " ")
         (let ([rest (cellV-second cell)])
           (type-case Value rest
             [nullV () (display "") ]; null at the end of the list is not printed
             [cellV (first second) (print-list rest)]
             [else (begin (display ".")
                        (print-value (cellV-second cell)))]))
         )
  )

; Exemplos
(test (interpS '(equal? 1 1)) (boolV #t))

(test (interpS '(equal? 1 2)) (boolV #f))

(test (interpS '(equal? (+ 4 2) (- 8 2))) (boolV #t))

(test (interpS '(equal? (lambda x (+ x x)) (lambda y (+ y y))))
      (boolV #f))

(interpS '(let ((a (+ 3 4))) (seq (display a) (+ 3 4))))

(interpS '(let ((a (+ 3 4)))
              (seq (display a)
                   (seq (+ a a)
                        (display a)))))
