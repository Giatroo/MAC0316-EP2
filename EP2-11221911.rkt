#lang plai-typed


; Basic expressions
(define-type ExprC
  [numC     (n : number)]
  [idC      (s : symbol)]
  [boolC    (b : boolean)]
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
  [consC    (car : ExprC) (cdr : ExprC)]
  [carC     (cell : ExprC)]
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
    [numS     (n)             (numC n)]
    [boolS    (b)             (boolC b)]
    [idS      (s)             (idC s)]
    [lamS     (a b)           (lamC a (desugar b))]
    [appS     (fun arg)       (appC (desugar fun) (desugar arg))]
    [plusS    (l r)           (plusC (desugar l) (desugar r))]
    [multS    (l r)           (multC (desugar l) (desugar r))]
    [bminusS  (l r)           (plusC (desugar l) (multC (numC -1) (desugar r)))]
    [uminusS  (e)             (multC (numC -1) (desugar e))]
    [ifS      (c s n)         (ifC (desugar c) (desugar s) (desugar n))]
    [seqS     (e1 e2)         (seqC (desugar e1) (desugar e2))]
    [letS     (n a b)         (letC n (desugar a) (desugar b))]
    [let*S    (n1 a1 n2 a2 b) (let*C n1 (desugar a1) n2 (desugar a2) (desugar b))]
    [letrecS  (n a b)         (letrecC n (desugar a) (desugar b))]
    [equal?S  (e1 e2)         (equal?C (desugar e1) (desugar e2))]
    [consS    (car cdr)       (consC (desugar car) (desugar cdr))]
    [carS     (exp)           (carC (desugar  exp))]
    [cdrS     (exp)           (cdrC (desugar  exp))]
    [displayS (exp)           (displayC (desugar exp))]
    [quoteS   (sym)           (quoteC sym)]
    [nullS    ()              (nullC)]
    ))


; We need a new value for the box
(define-type Value
  [numV     (n : number)]
  [boolV    (b : boolean)]
  [quoteV   (symb : symbol)]
  [closV    (arg : symbol) (body : ExprC) (env : Env)]
  [cellV    (first : (boxof Value)) (second : (boxof Value))]
  [suspendV (body : ExprC) (env : Env)]
  [boxV     (b : (boxof Value))]
  [nullV ]
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

(define (strict [v : Value] [flag : boolean]) : Value
  (type-case Value v
    [suspendV (b e) (if flag (strict (interp b e) flag) v)]
    [boxV     (b)   (if flag (begin (set-box! b (strict (unbox b) flag)) (unbox b)) (unbox b))]
    [else           v]
  )
)

; Interpreter
(define (interp [a : ExprC] [env : Env]) : Value
  (type-case ExprC a
    ; Numbers just evaluta to their equivalent Value
    [numC (n) (numV n)]

    [boolC (b) (boolV b)]

    ; IDs are retrieved from the Env and unboxed
    [idC (n) (boxV (lookup n env))]


    ; Lambdas evaluate to closures, which save the environment
    [lamC (a b) (closV a b env)]

    ; Application of function
    [appC (f a)
          (let ([f-value (strict (interp f env) #t)])
            (strict (interp (closV-body f-value)
                    (extend-env
                        (bind (closV-arg f-value) (box (suspendV a env)))
                        (closV-env f-value)
                    )) #t))]


    ; Sum two numbers using auxiliary function
    [plusC (l r)
        (num+ (strict (interp l env) #t)
              (strict (interp r env) #t))]

    ; Multiplies two numbers using auxiliary function
    [multC (l r)
        (num* (strict (interp l env) #t)
              (strict (interp r env) #t))]


    ; Conditional operator
    [ifC (c s n) (if (boolV-b (strict (interp c env) #t)) (strict (interp s env) #f) (strict (interp n env) #f))]

    ; Sequence of operations
    [seqC (b1 b2) (begin (strict (interp b1 env) #f) (strict (interp b2 env) #f))]


    ; Declaration of variable
    [letC (name arg body)
      (let* ([new-bind (bind name (box (suspendV arg env)))]
             [new-env (extend-env new-bind env)])
            (strict (interp body new-env) #f))]

    [let*C (name1 arg1 name2 arg2 body)
      (strict (interp (letC name1 arg1 (letC name2 arg2 body)) env) #f)]

    [letrecC (n a b)
      (let* ([mybox (box (nullV))] [new-env (extend-env [bind n mybox] env)])
          (begin (set-box! mybox (suspendV a new-env)) (strict (interp b new-env) #f)))]


    [equal?C (e1 e2)
      (boolV (equal? (strict (interp e1 env) #t) (strict (interp e2 env) #t)))]


    ; Cell operations
    [consC (car cdr) (cellV (box (suspendV car env)) (box (suspendV cdr env)))]

    [carC (exp)
      (let* ([x (strict (interp exp env) #t)] [caixa (cellV-first (strict x #t))])
          (begin (set-box! caixa (strict (unbox caixa) #t)) (unbox caixa)))]

    [cdrC (exp)
      (let* ([x (strict (interp exp env) #t)] [caixa (cellV-second x)])
          (begin (set-box! caixa (strict (unbox caixa) #t)) (unbox caixa)))]


    ;Display values
    [displayC (exp) (let ((value (strict (interp exp env) #f)))
                      (begin (print-value (strict (interp exp env) #f))
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
      [boolV  (b)     (display b)]
      [quoteV (symb)  (display symb)]
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
      [nullV    ()    (display '())]
      [boxV     (b)   (display b)]
      [suspendV (b e) (display "suspV")]
   )
)

(define (print-list cell) : void
  (begin
         (print-value (unbox (cellV-first cell)))
         (display " ")
         (let ([rest (unbox (cellV-second cell))])
           (type-case Value rest
             [nullV () (display "") ]; null at the end of the list is not printed
             [cellV (first second) (print-list rest)]
             [else (begin (display ".")
                        (print-value (unbox (cellV-second cell))))]))
         )
  )

; Exemplos e testes
; IMPORTANTE: Alguns desses testes foram compartilhados entre os alunos.
; Alguns testes foram criados por mim e disponibilizados aos outros alunos
; e alguns testes foram criados por outros alunos e disponibilizados para mim.
(test (interpS '(equal? 1 1)) (boolV #t))

(test (interpS '(equal? 1 2)) (boolV #f))

(test (interpS '(equal? (+ 4 2) (- 8 2))) (boolV #t))

(test (interpS '(equal? (lambda x (+ x x)) (lambda y (+ y y))))
      (boolV #f))

(interpS '(let ((a (+ 3 4))) (seq (display a) (+ 3 4))))
; should be equal to:
; suspV;(numV 7)

(interpS '(let ((a (+ 3 4)))
              (seq (display a)
                   (seq (+ a a)
                        (display a)))))
; should be equal to:
; suspV;7;(numV 7)

(interpS '(let* ((a (+ 3 4)) (b a))
              (seq (display a)
                   (seq (+ b b)
                        (display a)))))

; should be equal to:
; suspV;7;(numV 7)

;(interpS '(letrec ((f (lambda x (+ x (call f (- x 1))))))
;             (call f 5)))
; infinite function example

(test (interpS '(letrec ((f (lambda x (if (equal? x 0) 0 (+ x (call f (- x 1)))))))
             (call f 5)))
      (numV 15))

(test (interpS '(letrec ((f (lambda x (if (equal? x 1) 1 (* x (call f (- x 1)))))))
             (call f 5)))
      (numV 120))

(test (interpS '(call (lambda x x) 1))
    (numV 1))

; Os testes a seguir estão comentados para não ficar muita coisa na tela e não
; demorara na hora de carregar o código.
; Eles foram disponibilizados pelos alunos Lourenço e Miguel.
;(interpS '(cons 1 (cons 2 ())))
;(interpS '(car (cons 1 (cons 2 ()))))
;(interpS '(+ (car (cons 1 (cons 2 ()))) 2))
;(interpS '(let ([x (+ 3 3)]) (display x)))
;(interpS '(let ([x (+ 3 3)]) (seq (+ x x) x)))
;(interpS '(let ([x (+ 3 3)]) (call (lambda x (+ x x)) x)))
;(interpS '(let ([x (lambda y (+ y y))]) (+ (call x 2)  (call x 2))))
;(interpS '(let* ((x (+ 3 3)) (y x)) (seq (display y) (seq (display x) x))))
;(interpS '(let* ((x (+ 3 3)) (y x)) (seq (display x) (seq (display y) x))))
;(interpS '(call (car (cdr (cons 1 (cons (lambda x (+ x x)) ())))) 2))
;(interpS '(let ((y (call (lambda x (+ x x)) 6))) (call (lambda x (+ x x)) y)))
;(interpS '(let ((y (call (lambda x (+ x x)) 6))) (call (lambda x (+ x x)) 5)))
;(interpS '(let ((y (call (lambda x (+ x x)) 6))) (call (lambda x (cons 1 ())) 1)))
;(interpS '(let ((y (call (lambda x (+ x x)) 6))) (call (lambda x 5) y)))
;(interpS '(call (lambda x (+ x x)) 1))
