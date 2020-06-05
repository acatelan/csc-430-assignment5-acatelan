#lang typed/racket

(require typed/rackunit)

(define-type ExprC (U numC idC strC listC recordC ifC funC AppC))
(struct numC ([num : Real])
  #:transparent)
(struct idC ([sym : Symbol])
  #:transparent)
(struct strC ([str : String])
  #:transparent)
(struct listC ([l : (Listof ExprC)])
  #:transparent)
(struct recordC ([sym : (Listof Symbol)] [e : (Listof ExprC)])
  #:transparent)
(struct ifC ([test : ExprC] [ifThen : ExprC] [ifElse : ExprC])
  #:transparent)
(struct funC ([vars : (Listof Symbol)] [body : ExprC])
  #:transparent)
(struct AppC ([f : ExprC] [args : (Listof ExprC)])
  #:transparent)

(define-type Value (U numV boolV strV listV recordV closV primOpV))
(struct numV ([num : Real])
  #:transparent)
(struct boolV ([bool : Boolean])
  #:transparent)
(struct strV ([str : String])
  #:transparent)
(struct listV ([l : (Listof Value)])
  #:transparent)
(struct recordV ([sym : (Listof Symbol)] [v : (Listof Value)])
  #:transparent)
(struct closV ([args : (Listof Symbol)] [body : ExprC] [env : Env])
  #:transparent)
(struct primOpV ([op : Symbol])
  #:transparent)

(define-type Binding (U bind))
(struct bind ([name : Symbol] [val : Value])
  #:transparent)

(define-type-alias Env (Listof Binding))
(define top-env
  (list
   (bind '+ (primOpV '+))
   (bind '- (primOpV '-))
   (bind '* (primOpV '*))
   (bind '/ (primOpV '/))
   (bind '++ (primOpV '++))
   (bind '== (primOpV '==))
   (bind 'True (boolV #t))
   (bind 'False (boolV #f))))
(define extend-env cons)

(define (top-interp [e : ExprC]) : String
  (serialize (interp e top-env)))

(define (serialize [v : Value]) : String
  (match v
    [(numV n)
     (number->string n)]
    [(boolV b)
     (if b "True" "False")]
    [(strV str)
     str]
    [(listV l)
     (if (equal? 1 (length l))
         (serialize (first l))
         (string-append (serialize (first l)) ", " (serialize (listV (rest l)))))]
    [(recordV sym e)
     (if (equal? 1 (length e))
         (string-append (symbol->string (first sym)) ": " (serialize (first e)))
         (string-append (symbol->string (first sym)) ": " (serialize (first e)) ", " (serialize (recordV (rest sym) (rest e)))))]
    [(closV args body env)
     "<function>"]
    [(primOpV op)
     "<primOp>"]))

(define (interp [e : ExprC] [env : Env]) : Value
  (match e
    [(numC n)
     (numV n)]
    [(idC sym)
     (lookup sym env)]
    [(strC str)
     (strV str)]
    [(listC lst)
     (listV (map (lambda (l) (interp (cast l ExprC) env)) lst))]
    [(recordC sym e)
     (recordV sym (map (lambda (exp) (interp (cast exp ExprC) env)) e))]
    [(ifC test ifThen ifElse)
     (define check (interp test env))
     (cond
       [(boolV? check)
        (if (boolV-bool check) (interp ifThen env) (interp ifElse env))]
       [else
        (error "AQSE, if given non-boolV test - "check)])]
    [(funC vars body)
     (closV vars body env)]
    [(AppC f args)
     (define f-value (interp f env))
     (cond
       [(closV? f-value)
        (interp (closV-body f-value) (extend-env-helper args (closV-args f-value) env (closV-env f-value)))]
       [(primOpV? f-value)
        (calcPrim f-value (map (lambda (v) (interp (cast v ExprC) env)) args) env)]
       [else
        (error "AQSE, invalid function for AppC - "f)])]))

; given an identifier, looks for that symbol in the environment and returns its value, if it exists
(define (lookup [for : Symbol] [env : Env]) : Value
  (cond
    [(empty? env)
     (error "AQSE, identifier could not be found in lookup - "for)]
    [else
     (cond
       [(symbol=? for (bind-name (first env)))
        (bind-val (first env))]
       [else
        (lookup for (rest env))])]))

; helper function that extends env through the args of an AppC
(define (extend-env-helper [args : (Listof ExprC)] [vars : (Listof Symbol)] [env : Env] [cenv : Env]) : Env
  (cond
    [(= (length args) (length vars))
     (cond
       [(= (length args) 0)
        cenv]
       [(= (length args) 1)
        (extend-env (bind (first vars) (interp (first args) env)) cenv)]
       [else
        (define extended-env (extend-env-helper (rest args) (rest vars) env cenv))
        (extend-env (bind (first vars) (interp (first args) env)) extended-env)])]
    [else
     (error "AQSE, invalid number of arguments, given "(length args)" expected "(length vars))]))

; calculates the value of primitives
(define (calcPrim [f : primOpV] [vals : (Listof Value)] [env : Env]) : Value
  (match vals
    [(list (? numV? v))
     (match (primOpV-op f)
       [(or '+ '- '* '/)
        (if (numV? v)
            v
            (error "AQSE, invalid argument for "(primOpV-op f)" - "v))]
       [else
        (error "AQSE, unknown primOp - "(primOpV-op f))])]
    [(list (? strV? v))
     (match (primOpV-op f)
       ['++
        (if (strV? v)
            v
            (error "AQSE, invalid argument for '++ - "v))]
       [else
        (error "AQSE, unknown primOp - "(primOpV-op f))])]
    [(list (? numV? v) ...)
     (match (primOpV-op f)
       ['+
        (if (numV? (first vals))
            (numV (+ (numV-num (cast (first vals) numV)) (numV-num (cast (calcPrim f (rest vals) env) numV))))
            (error "AQSE, invalid argument for '+ - "(first vals)))]
       ['-
        (if (numV? (first vals))
            (numV (- (numV-num (cast (first vals) numV)) (numV-num (cast (calcPrim f (rest vals) env) numV))))
            (error "AQSE, invalid argument for '- - "(first vals)))]
       ['*
        (if (numV? (first vals))
            (numV (* (numV-num (cast (first vals) numV)) (numV-num (cast (calcPrim f (rest vals) env) numV))))
            (error "AQSE, invalid argument for '* - "(first vals)))]
       ['/
        (if (numV? (first vals))
            (numV (/ (numV-num (cast (first vals) numV)) (numV-num (cast (calcPrim f (rest vals) env) numV))))
            (error "AQSE, invalid argument for '/ - "(first vals)))]
       ['==
        (if (and (numV? (first vals)) (numV? (second vals)))
            (boolV (equal? (numV-num (cast (first vals) numV)) (numV-num (cast (second vals) numV))))
            (error "AQSE, invalid arguments for '== "(first vals)" "(second vals)))]
       [else
        (error "AQSE, invalid primOp - "(primOpV-op f))])]
    [(list (? strV? v) ...)
     (match (primOpV-op f)
       ['++
        (if (strV? (first vals))
            (strV (string-append (strV-str (cast (first vals) strV)) (strV-str (cast (calcPrim f (rest vals) env) strV))))
            (error "AQSE, invalid argument for '++ - "(first vals)))]
       ['==
        (if (and (strV? (first vals)) (strV? (second vals)))
            (boolV (equal? (strV-str (cast (first vals) strV)) (strV-str (cast (second vals) strV))))
            (error "AQSE, invalid arguments for '== "(first vals)" "(second vals)))]
       [else
        (error "AQSE, invalid primOp - "(primOpV-op f))])]
    [else
     (error "AQSE, invalid vals - "vals)]))

;; tests
(check-equal? (top-interp (numC 1)) "1")
(check-equal? (top-interp (idC 'True)) "True")
(check-equal? (top-interp (idC 'False)) "False")
(check-equal? (top-interp (strC "Hello!")) "Hello!")
(check-equal? (top-interp (funC (list 'name) (idC 'name))) "<function>")
(check-equal? (top-interp (idC '+)) "<primOp>")
(check-equal? (top-interp (AppC (funC (list 'x 'y) (AppC (idC '+) (list (idC 'x) (idC 'y)))) (list (numC 1) (numC 2)))) "3")
(check-equal? (top-interp (AppC (funC (list 'x 'y) (AppC (idC '-) (list (idC 'x) (idC 'y)))) (list (numC 5) (numC 2)))) "3")
(check-equal? (top-interp (AppC (funC (list 'x 'y) (AppC (idC '*) (list (idC 'x) (idC 'y)))) (list (numC 1) (numC 2)))) "2")
(check-equal? (top-interp (AppC (funC (list 'x 'y) (AppC (idC '/) (list (idC 'x) (idC 'y)))) (list (numC 2) (numC 2)))) "1")
(check-equal? (top-interp (AppC (funC (list 'name) (AppC (idC '++) (list (strC "Hello ") (idC 'name) (strC "!")))) (list (strC "Anthony")))) "Hello Anthony!")
(check-equal? (top-interp (AppC (funC (list 'name) (ifC
                                                    (AppC (idC '==) (list (idC 'name) (strC "Abraham Lincoln")))
                                                    (strC "Greetings, Mr. President")
                                                    (strC "Hey!")))
                                (list (strC "Abraham Lincoln")))) "Greetings, Mr. President")
(check-equal? (top-interp (AppC (funC (list 'name) (ifC
                                                    (AppC (idC '==) (list (idC 'name) (strC "Abraham Lincoln")))
                                                    (strC "Greetings, Mr. President")
                                                    (strC "Hey!")))
                                (list (strC "Anthony")))) "Hey!")
(check-equal? (top-interp (AppC (funC (list 'name) (ifC
                                                    (AppC (idC '==) (list (idC 'name) (strC "Abraham Lincoln")))
                                                    (listC (list (idC 'True) (strC "Greetings, Mr. President")))
                                                    (listC (list (idC 'False) (strC "Hey!")))))
                                (list (strC "Anthony")))) "False, Hey!")
(check-equal? (top-interp (recordC (list 'x 'y 'z) (list (numC 5) (strC "Hi!") (idC 'True)))) "x: 5, y: Hi!, z: True")
(check-exn exn:fail? (lambda () (top-interp (idC 'x))))