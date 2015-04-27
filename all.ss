;:  Single-file version of the interpreter.
;; Easier to submit to server, probably harder to use in the development process

(load "chez-init.ss")

;-------------------+
;                   |
;    DATATYPES      |
;                   |
;-------------------+

; parsed expression

(define-datatype expression expression?
  [var-exp
    (id symbol?)]
  [lit-exp
    (id (lambda (x)
      (ormap
       (lambda (pred) (pred x))
       (list number? vector? boolean? symbol? string? pair? list? null?))))]
  [quote-exp
    (body expression?)]
  [lambda-exp
    (id list?)
    (body (list-of expression?))]
  [lambda-exp-variable
    (variable symbol?) ;; make pair
    (id list?)
    (body (list-of expression?))]
  [if-else-exp
    (pred expression?)
    (yes expression?)
    (no expression?)]
  [if-exp
    (pred expression?)
    (yes expression?)]
  [set!-exp
    (var expression?)
    (body expression?)]
  [let-exp
    (variables (list-of list?))
    (body (list-of expression?))]
  [let*-exp
    (variables (list-of list?))
    (body (list-of expression?))]
  [letrec-exp
    (variables (list-of list?))
    (body (list-of expression?))]
  [empty-app-exp
    (rator expression?)]
  [app-exp
    (rator expression?)
    (rand (list-of expression?))]
)

;; environment type definitions

(define scheme-value?
  (lambda (x) #t))

(define-datatype environment environment?
  (empty-env-record)
  (extended-env-record
   (syms (list-of symbol?))
   (vals (list-of scheme-value?))
   (env environment?)))

; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
  [prim-proc
    (name symbol?)]
  [closure
    (symbols (list-of symbol?))
    (body (list-of expression?))
    (env environment?)]
)



;-------------------+
;                   |
;    PARSER         |
;                   |
;-------------------+


; This is a parser for simple Scheme expressions, such as those in EOPL, 3.1 thru 3.3.

; You will want to replace this with your parser that includes more expression types, more options for these types, and error-checking.

; Procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)

(define parse-exp
  (lambda (datum)
    (cond
      [(symbol? datum) (var-exp datum)]
      [(or (number? datum) (string? datum) (boolean? datum) (vector? datum)) (lit-exp datum)]
      [(pair? datum)
        (cond
          [(eqv? (car datum) 'lambda)
            (if (or (null? (cdr datum)) (null? (cddr datum)))
              (eopl:error 'parse-exp "incorrect # of arguments: ~s" datum)
              (if (list? (cadr datum))
                (if ((lambda (x) (not (andmap symbol? x))) (cadr datum))
                  (eopl:error 'parse-exp "incorrect arguments: ~s in ~s" (cadr datum) datum)
                  (lambda-exp (cadr datum)
                              (map parse-exp (cddr datum)))
                )
                (lambda-exp-variable 'variable (list (cadr datum))
                            (map parse-exp (cddr datum)))
              ))]

          [(eqv? (car datum) 'if)
            (if (or (null? (cdr datum)) (null? (cddr datum)))
              (eopl:error 'parse-exp "incorrect # of arguments: ~s" datum)
              (if (null? (cdddr datum))
                (if-exp
                  (parse-exp (cadr datum))
                  (parse-exp (caddr datum)))
                (if-else-exp
                  (parse-exp (cadr datum))
                  (parse-exp (caddr datum))
                  (parse-exp (cadddr datum)))))]

          [(eqv? (car datum) 'set!)
            (if (or (null? (cdr datum)) (null? (cddr datum)) (not (null? (cdddr datum))))
              (eopl:error 'parse-exp "incorrect # of arguments: ~s" datum)
              (set!-exp
                (parse-exp (cadr datum))
                (parse-exp (caddr datum))))]

          [(eqv? (car datum) 'let)
            (if (or (null? (cdr datum)) (null? (cddr datum)))
              (eopl:error 'parse-exp "incorrect # of arguments: ~s" datum)
              (if (or (not (list? (cadr datum))))
                (eopl:error 'parse-exp "incorrect argument(s): ~s" datum)
                (let-exp
                  (map (lambda (x) (if (or (not (list? x)) (null? (cdr x)) (not (null? (cddr x))) (not (symbol? (car x))))
                          (eopl:error 'parse-exp "incorrect argument(s): ~s in ~s" x datum)
                          (list
                                  (parse-exp (car x))
                                  (parse-exp (cadr x)))))
                    (cadr datum))
                  (map parse-exp (cddr datum)))))]

          [(eqv? (car datum) 'let*)
            (if (or (null? (cdr datum)) (null? (cddr datum)))
              (eopl:error 'parse-exp "incorrect # of arguments: ~s" datum)
              (if (or (not (list? (cadr datum))))
                (eopl:error 'parse-exp "incorrect argument(s): ~s" datum)
                (let*-exp
                  (map (lambda (x) (if (or (not (list? x)) (null? (cdr x)) (not (null? (cddr x))) (not (symbol? (car x))))
                          (eopl:error 'parse-exp "incorrect argument(s): ~s in ~s" x datum)
                          (list
                                  (parse-exp (car x))
                                  (parse-exp (cadr x)))))
                      (cadr datum))
                  (map parse-exp (cddr datum)))))]

          [(eqv? (car datum) 'letrec)
            (if (or (null? (cdr datum)) (null? (cddr datum)))
              (eopl:error 'parse-exp "incorrect # of arguments: ~s" datum)
              (if (or (not (list? (cadr datum))))
                (eopl:error 'parse-exp "incorrect argument(s): ~s" datum)
                (letrec-exp
                  (map (lambda (x) (if (or (not (list? x)) (null? (cdr x)) (not (null? (cddr x))) (not (symbol? (car x))))
                          (eopl:error 'parse-exp "incorrect argument(s): ~s in ~s" x datum)
                          (list
                                  (parse-exp (car x))
                                  (parse-exp (cadr x)))))
                    (cadr datum))
                  (map parse-exp (cddr datum)))))]

          [(eqv? (car datum) 'quote)
            (quote-exp (lit-exp (cadr datum)))]

          [else (if (not (list? datum))
                  (eopl:error 'parse-exp "Improper list: ~s" datum)
                  (if (null? (cdr datum))
                          (empty-app-exp (parse-exp (car datum)))
                          (app-exp (parse-exp (car datum))
                		            (map parse-exp (cdr datum)))))]
        )]
      [else
        (eopl:error 'parse-exp "bad expression: ~s" datum)]
    )
  )
)

(define unparse-exp
  (lambda (exp)
    (cases expression exp
      [var-exp (id) id]
      [lit-exp (id) id]
      [lambda-exp (id body)
        (append (list 'lambda id) (map unparse-exp body))]
      [lambda-exp-variable (variable id body)
        (append (list 'lambda (car id)) (map unparse-exp body))]
      [if-else-exp (pred yes no)
        (append
          (append
            (list 'if)
            (list (unparse-exp pred)))
          (list (unparse-exp yes) (unparse-exp no)))]
      [if-exp (pred yes)
        (append
          (append
            (list 'if)
            (list (unparse-exp pred)))
          (list (unparse-exp yes)))]
      [set!-exp (var body)
        (list 'set! (unparse-exp var) (unparse-exp body))]
      [let-exp (variables body)
        (append (list 'let (map (lambda (x)
                                  (list (unparse-exp (car x)) (unparse-exp (cadr x))))
                                 variables)) (map unparse-exp body))]
      [let*-exp (variables body)
        (append (list 'let* (map (lambda (x)
                                  (list (unparse-exp (car x)) (unparse-exp (cadr x))))
                                 variables)) (map unparse-exp body))]
      [letrec-exp (variables body)
        (append (list 'letrec (map (lambda (x)
                                  (list (unparse-exp (car x)) (unparse-exp (cadr x))))
                                 variables)) (map unparse-exp body))]
      [quote-exp (body)
        (unparse-exp body)]
      [empty-app-exp (rator)
        (list (unparse-exp rator))]
      [app-exp (rator rand)
        (append (list (unparse-exp rator)) (map unparse-exp rand))]
    )
  )
)

;-------------------+
;                   |
;   ENVIRONMENTS    |
;                   |
;-------------------+





; Environment definitions for CSSE 304 Scheme interpreter.  Based on EoPL section 2.3

(define empty-env
  (lambda ()
    (empty-env-record)))

(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms vals env)))

(define list-find-position
  (lambda (sym los)
    (list-index (lambda (xsym) (eqv? sym xsym)) los)))

(define list-index
  (lambda (pred ls)
    (cond
     ((null? ls) #f)
     ((pred (car ls)) 0)
     (else (let ((list-index-r (list-index pred (cdr ls))))
	     (if (number? list-index-r)
		      (+ 1 list-index-r)
		      #f))))))

(define apply-env
  (lambda (env sym succeed fail) ; succeed and fail are procedures applied if the var is or isn't found, respectively.
    (cases environment env
      (empty-env-record ()
        (fail))
      (extended-env-record (syms vals env)
	      (let ((pos (list-find-position sym syms)))
      	  (if (number? pos)
	         (succeed (list-ref vals pos))
	         (apply-env env sym succeed fail)))))))



;-----------------------+
;                       |
;   SYNTAX EXPANSION    |
;                       |
;-----------------------+



; To be added later









;-------------------+
;                   |
;   INTERPRETER     |
;                   |
;-------------------+



; top-level-eval evaluates a form in the global environment

(define top-level-eval
  (lambda (form)
    ; later we may add things that are not expressions.
    (eval-exp form init-env)))

; eval-exp is the main component of the interpreter

(define eval-exp
  (lambda (exp env) ; add environment
    (cases expression exp
      [lit-exp (datum) datum]
      [var-exp (id)
				(apply-env env id; look up its value.
      	   (lambda (x) x) ; procedure to call if id is in the environment
           (lambda () (eopl:error 'apply-env ; procedure to call if id not in env
		          "variable not found in environment: ~s"
			   id)))]
      [quote-exp (body) (eval-exp body env)]
      [if-else-exp (pred true false)
        (if (eval-exp pred env)
            (eval-exp true env)
            (eval-exp false env))]
      [let-exp (variables body)
        (let ((new-env (extend-env (map (lambda (x) (unparse-exp (car x))) variables) (map (lambda (x) (eval-exp (cadr x) env)) variables) env)))
          (letrec ([amama
                    (lambda (expl)
                      (if (null? expl)
                        '()
                        (if (null? (cdr expl))
                          (eval-exp (car expl) new-env)
                          (begin
                            (eval-exp (car expl) new-env)
                            (amama (cdr expl))
                          ))))])
              (amama body)))]
      [lambda-exp (id body) (closure id body env)]
      [app-exp (rator rands)
        (let ([proc-value (eval-exp rator env)]
              [args (eval-rands rands env)])
          (apply-proc proc-value args))]
      [else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)])))


(define eval-inorder
  (lambda (body env)
    (if (null? body)
      '()
      (if (null? (cdr body))
        (eval-exp (car body) env)
        (begin
          (eval-exp (car body) env)
          (eval-inorder (cdr body) env))))))

; evaluate the list of operands, putting results into a list
(define eval-rands
  (lambda (rands env)
    (map (lambda (x) (eval-exp x env)) rands)))

;  Apply a procedure to its arguments.

(define apply-proc
  (lambda (proc-value args)
    (cases proc-val proc-value
      [prim-proc (op) (apply-prim-proc op args)]
			; You will add other cases
      [closure (syms body env) (eval-inorder body (extend-env syms args env))]
      [else (eopl:error 'apply-proc
                   "Attempt to apply bad procedure: ~s"
                    proc-value)])))

(define *prim-proc-names* '(+ - * / add1 sub1 = > < >= <= cons car cdr caar cadr cdar cddr caaar caadr cadar caddr cdaar cdadr cddar cdddr list zero? not null? assq eq? equal? atom? length list->vector list? pair? procedure? vector->list vector make-vector vector-ref vector? number? symbol? set-car! set-cdr! vector-set! display newline))

(define init-env         ; for now, our initial global environment only contains
  (extend-env            ; procedure names.  Recall that an environment associates
     *prim-proc-names*   ;  a value (not an expression) with an identifier.
     (map prim-proc
          *prim-proc-names*)
     (empty-env)))

; Usually an interpreter must define each
; built-in procedure individually.  We are "cheating" a little bit.

(define apply-prim-proc
  (lambda (prim-proc args)
    (case prim-proc
      [(+) (apply + args)]
      [(-) (apply - args)]
      [(*) (apply * args)]
      [(/) (apply / args)]
      [(add1) (if (null? (cdr args))
                  (+ (1st args) 1)
                  (error 'apply-prim-proc "Incorrect number of arguments to" prim-proc))]
      [(sub1) (if (null? (cdr args))
                  (- (1st args) 1)
                  (error 'apply-prim-proc "Incorrect number of arguments to" prim-proc))]
      [(=) (apply = args)]
      [(<) (apply < args)]
      [(>) (apply > args)]
      [(<=) (apply <= args)]
      [(>=) (apply >= args)]
      [(cons) (apply cons args)]

      [(car) (if (null? (cdr args))
                  (car (1st args))
                  (error 'apply-prim-proc "Incorrect number of arguments to" prim-proc))]
      [(cdr) (if (null? (cdr args))
                  (cdr (1st args))
                  (error 'apply-prim-proc "Incorrect number of arguments to" prim-proc))]
      [(caar) (if (null? (cdr args))
                  (caar (1st args))
                  (error 'apply-prim-proc "Incorrect number of arguments to" prim-proc))]
      [(cadr) (if (null? (cdr args))
                  (cadr (1st args))
                  (error 'apply-prim-proc "Incorrect number of arguments to" prim-proc))]
      [(cdar) (if (null? (cdr args))
                  (cdar (1st args))
                  (error 'apply-prim-proc "Incorrect number of arguments to" prim-proc))]
      [(cddr) (if (null? (cdr args))
                  (cddr (1st args))
                  (error 'apply-prim-proc "Incorrect number of arguments to" prim-proc))]
      [(caaar) (if (null? (cdr args))
                  (caaar (1st args))
                  (error 'apply-prim-proc "Incorrect number of arguments to" prim-proc))]
      [(caadr) (if (null? (cdr args))
                  (caadr (1st args))
                  (error 'apply-prim-proc "Incorrect number of arguments to" prim-proc))]
      [(cadar) (if (null? (cdr args))
                  (cadar (1st args))
                  (error 'apply-prim-proc "Incorrect number of arguments to" prim-proc))]
      [(caddr) (if (null? (cdr args))
                  (caddr (1st args))
                  (error 'apply-prim-proc "Incorrect number of arguments to" prim-proc))]
      [(cdaar) (if (null? (cdr args))
                  (cdaar (1st args))
                  (error 'apply-prim-proc "Incorrect number of arguments to" prim-proc))]
      [(cdadr) (if (null? (cdr args))
                  (cdadr (1st args))
                  (error 'apply-prim-proc "Incorrect number of arguments to" prim-proc))]
      [(cddar) (if (null? (cdr args))
                  (cddar (1st args))
                  (error 'apply-prim-proc "Incorrect number of arguments to" prim-proc))]
      [(cdddr) (if (null? (cdr args))
                  (cdddr (1st args))
                  (error 'apply-prim-proc "Incorrect number of arguments to" prim-proc))]

      [(list) args]
      [(zero?) (if (null? (cdr args))
                  (zero? (1st args))
                  (error 'apply-prim-proc "Incorrect number of arguments to" prim-proc))]
      [(not) (if (null? (cdr args))
                  (not (1st args))
                  (error 'apply-prim-proc "Incorrect number of arguments to" prim-proc))]
      [(null?) (if (null? (cdr args))
                  (null? (1st args))
                  (error 'apply-prim-proc "Incorrect number of arguments to" prim-proc))]
      [(assq) (assq (1st args) (2nd args))]
      [(eq?) (apply eq? args)]
      [(equal?) (apply equal? args)]
      [(atom?)
        (if (null? (cdr args))
            (atom? (1st args))
            (error 'apply-prim-proc "Incorrect number of arguments to" prim-proc))]
      [(length)
        (if (null? (cdr args))
          (length (1st args))
          (error 'apply-prim-proc "Incorrect number of arguments to" prim-proc))]
      [(list->vector)
        (if (null? (cdr args))
          (list->vector (1st args))
          (error 'apply-prim-proc "Incorrect number of arguments to" prim-proc))]
      [(list?)
        (if (null? (cdr args))
          (list? (1st args))
          (error 'apply-prim-proc "Incorrect number of arguments to" prim-proc))]
      [(pair?)
        (if (null? (cdr args))
          (pair? (1st args))
          (error 'apply-prim-proc "Incorrect number of arguments to" prim-proc))]
      [(procedure?)
        (if (null? (cdr args))
          (proc-val? (1st args))
          (error 'apply-prim-proc "Incorrect number of arguments to" prim-proc))]
      [(vector->list)
        (if (null? (cdr args))
          (vector->list (1st args))
          (error 'apply-prim-proc "Incorrect number of arguments to" prim-proc))]
      [(vector) (vector args)]
      [(make-vector) (make-vector (1st args) (2nd args))]
      [(vector-ref) (vector-ref (1st args) (2nd args))]
      [(vector?)
        (if (null? (cdr args))
          (vector? (1st args))
          (error 'apply-prim-proc "Incorrect number of arguments to" prim-proc))]
      [(number?)
        (if (null? (cdr args))
          (number? (1st args))
          (error 'apply-prim-proc "Incorrect number of arguments to" prim-proc))]
      [(symbol?)
        (if (null? (cdr args))
          (symbol? (1st args))
          (error 'apply-prim-proc "Incorrect number of arguments to" prim-proc))]
      [(set-car!) (set-car! (1st args) (2nd args))]
      [(set-cdr!) (set-cdr! (1st args) (2nd args))]
      [(vector-set!) (vector-set! (1st args) (2nd args) (3rd args))]
      [(display) (apply display args)]
      [(newline) (newline)]
      [else (error 'apply-prim-proc
            "Bad primitive procedure name: ~s"
            prim-proc)])))

(define rep      ; "read-eval-print" loop.
  (lambda ()
    (display "--> ")
    ;; notice that we don't save changes to the environment...
    (let ([answer (top-level-eval (parse-exp (read)))])
      ;; TODO: are there answers that should display differently?
      (eopl:pretty-print answer) (newline)
      (rep))))  ; tail-recursive, so stack doesn't grow.

(define eval-one-exp
  (lambda (x) (top-level-eval (parse-exp x))))
