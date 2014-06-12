(declare (unit defs))

(use extras)

(define-record num-type type)
(define-record expr-type type)
(define-record bound-term ident)

(define-record term-const binding range)
(define-record term-var binding range)
(define-record term-op op operands)
(define-record permutation forms body type)

(define-record term-list l)
(define-record expression type lh rh bindings plist)

(define-record instance expr vals properties)

(define default-constant-range (cons -32 32))
(define default-variable-range '(a b c d e f g h i j k l m n o p q r s t u v w x y z))

(define flatten
  (lambda (l)
    (cond
      ((null? l) '())
      ((pair? l) (append (flatten (car l)) (flatten (cdr l))))
      (else (list l))
    )
  )
)

(define list-true?
  (lambda (l)
    (if (eqv? l '())
      #t
      (and (car l) (list-true? (cdr l)))
    )
  )
)

(define choose-from-list
  (lambda (l)
    (list-ref l (random (length l)))
  )
)

(define try
  (lambda (t #!optional handle)
    (handle-exceptions
      exn
      (if ((condition-predicate 'aql-except) exn)
        (if (procedure? handle)
          (handle ((condition-property-accessor 'aql-except 'msg) exn))
          (begin
            (display "error: ")
            (display ((condition-property-accessor 'aql-except 'msg) exn))
            (newline)
            (exit 1)
          )
        )
        (abort exn)
      )
      (t)
    )
  )
)

(define except
  (lambda (msg)
    (signal (make-property-condition 'aql-except 'msg msg))
  )
)

(define aql-assert
  (lambda (check msg)
    (unless check
      (except msg)
    )
  )
)

(define constant
  (lambda (type #!optional binding range)
    (aql-assert (num-type? type) "expected type as first argument to constant")
    (if binding
      (aql-assert (bound-term? binding) "expected binding or #f as second argument to constant")
    )
    (if range
      (aql-assert (or (pair? range) (list? range) (number? range)) "expected pair, list, or number as third argument to constant")
    )
    (make-term-const binding range)
  )
)

(define bind
  (lambda (ident)
    (aql-assert (symbol? ident) "expected symbol as argument to bind")
    (make-bound-term ident)
  )
)

(define variable
  (lambda (#!optional binding range)
    (if binding
      (aql-assert (bound-term? binding) "expected binding as first argument to variable")
    )
    (if range
      (aql-assert (list? range) "expected list as second argument to variable")
    )
    (make-term-var binding range)
  )
)

(define integer (make-num-type 'integer))
(define rational (make-num-type 'rational))
(define decimal (make-num-type 'decimal))

(define term-object?
  (lambda (t)
    (or (term-const? t) (term-var? t) (term-op? t) (permutation? t))
  )
)

(define valid-tlist?
  (lambda (tlist)
    (if (eqv? tlist '())
      #t
      (if (term-object? (car tlist))
        (valid-tlist? (cdr tlist))
        #f
      )
    )
  )
)

(define terms
  (lambda (#!rest tlist)
    (aql-assert (valid-tlist? tlist) "expected series of term objects as argument to terms")
    (make-term-list tlist)
  )
)


(define op+
  (lambda (#!rest opers)
    (make-term-op '+ opers)
  )
)

(define op-
  (lambda (#!rest opers)
    (make-term-op '- opers)
  )
)

(define op*
  (lambda (#!rest opers)
    (make-term-op '* opers)
  )
)

(define op^
  (lambda (b x)
    (make-term-op '^ (list b x))
  )
)

(define op/
  (lambda (#!rest opers)
    (make-term-op '/ opers)
  )
)

(define et-equality (make-expr-type '=))
(define et-inequality-gt (make-expr-type '>))
(define et-inequality-lt (make-expr-type '<))
(define et-inequality-gte (make-expr-type '>=))
(define et-inequality-lte (make-expr-type '<=))

(define equality
  (lambda (#!optional form)
    (case form
      ((#f) et-equality)
      ((=) et-equality)
      ((>) et-inequality-gt)
      ((<) et-inequality-lt)
      ((>=) et-inequality-gte)
      ((<=) et-inequality-lte)
    )
  )
)

(define extract-terms
  (lambda (t)
    (cond
      ((term-list? t) (term-list-l t))
      ((term-op? t) (term-op-operands t))
      ((permutation? t) (permutation-body t))
      (else #f)
    )
  )
)

(define extract-bindings
  (lambda (t)
    (let ((initial (extract-terms t)))
      (aql-assert initial "expected terms list or operator as first argument to extract-bindings")
      (let loop ((tlist initial) (b '()))
        (if (eqv? tlist '())
          b
          (let ((c (car tlist)))
            (let ((b2
                    (cond ((term-const? c) (term-const-binding c))
                          ((term-var? c) (term-var-binding c))
                          ((term-op? c) (let ((l (extract-bindings c)))
                                          (if (eqv? l '())
                                            #f
                                            l
                                          )
                                        ))
                          ((permutation? c) (let ((l (extract-bindings c)))
                                              (if (eqv? l '())
                                                #f
                                                l
                                              )
                                            ))
                   )
                 ))
              (loop (cdr tlist) (cons b2 b))
            )
          )
        )
      )
    )
  )
)

(define permutation-list
  (lambda (t)
    (let ((initial (extract-terms t)))
      (aql-assert initial "expected terms list or operator as first argument to permutation-list")
      (let loop ((p '()) (tlist initial))
        (if (eqv? tlist '())
          p
          (let ((term (car tlist)))
            (cond
              ((permutation? term) (loop 
                                     (let ((subpl (permutation-list term)))
;                                       (if (eqv? subpl '())
;                                         (cons (list (length (permutation-forms term))) p)
;                                         (cons (cons (length (permutation-forms term)) subpl) p)
;                                       )
                                       (cons (cons (length (permutation-forms term)) subpl) p)
                                     )
                                     (cdr tlist)
                                   ))
              ((term-op? term) (loop (cons (permutation-list term) p) (cdr tlist)))
              (else (loop p (cdr tlist)))
            )
          )
        )
      )
    )
  )
)

(define expression-pnum
  (lambda (expr)
    (apply * (flatten (expression-plist expr)))
  )
)

(define expression
  (lambda (type lh rh)
    (aql-assert (expr-type? type) "expected expression type as first argument to expression")
    (aql-assert (and (term-list? lh) (term-list? rh)) "expected term list as second and third argumnet to expression")
    (make-expression
      type
      lh
      rh
      (cons (extract-bindings lh) (extract-bindings rh))
      (cons (permutation-list lh) (permutation-list rh))
    )
  )
)

(define permute-type-maker
  (lambda (type)
    (lambda (#!rest forms)
      (lambda (#!rest body)
        (assert (or (list-true? (map procedure? forms)) (list-true? (map term-object? forms))) "expected a series of procedures or a series of term objects as argument to permutation")
        (make-permutation forms body type)
      )
    )
  )
)

(define random-permute (permute-type-maker 'random))
(define permute (permute-type-maker 'straight))
(define choose (permute-type-maker 'choice))

;(define resolve-permutations
;  (lambda (expr n)
;    (let loop ((res '()) (tlist (append (term-list-l (expression-lh expr)) (term-list-l (expression-rh expr)))) (pl (expression-plist expr)) (i n))
;      (if (eqv? tlist '())
;        res
;        (let ((term (car tlist)))
;          (cond
;            ((permutation? term) (loop
;                                   (cons
;                                     (loop
;                                       '()
;                                       (list ((list-ref (permutation-forms term) (modulo i (caar pl))) (permutation-body term)))
;                                       (car pl)
;                                       (quotient i (caar pl))
;                                     )
;                                     res
;                                   )
;                                   (cdr tlist)
;                                   (cdr pl)
;                                   (quotient i (apply * (flatten (car pl))))
;                                 ))
;            ((term-op? term) (loop
;                               (cons
;                                 (make-term-op
;                                   (term-op-op term)
;                                   (loop
;                                     '()
;                                     (term-op-operands term)
;                                     pl
;                                     i
;                                   )
;                                 )
;                                 res
;                               )
;                               (cdr tlist)
;                               pl
;                               i
;                            ))
;            (else (loop (cons term res) (cdr tlist) pl i))
;          )
;        )
;      )
;    )
;  )
;)
;

(define resolve-permutations
  (lambda (expr n)
    (letrec
       ((loop
         (lambda (res tlist pl i)
           (if (eqv? tlist '())
             res
             (let ((term (car tlist)))
               (cond
                 ((permutation? term) (let
                                        ((t (list-ref (permutation-forms term) (modulo i (caar pl))))
                                         (r (loop '() (permutation-body term) (cdar pl) (quotient i (caar pl)))))
                                        (loop
                                          (cons
                                            (if (procedure? t)
                                              (let ((b (apply t r)))
                                                (assert (valid-tlist? b) "expected permutation body to resolve to list of terms")
                                                b
                                              )
                                              t
                                            )
                                            res
                                          )
                                          (cdr tlist)
                                          (cdr pl)
                                          (quotient i (apply * (flatten (car pl))))
                                        )
                                      ))
                 ((term-op? term) (let
                                    ((r (loop '() (term-op-operands term) (car pl) i)))
                                    (loop
                                      (cons
                                        (make-term-op (term-op-op term) r)
                                        res
                                      )
                                      (cdr tlist)
                                      (cdr pl)
                                      (quotient i (let ((flat (flatten (car pl)))) (if (eqv? flat '()) 1 (apply * flat))))
                                    )
                                  ))
                 (else (loop (cons term res) (cdr tlist) pl i))
               )
             )
           )
         )
       ))
      (let* ((lh (loop '() (term-list-l (expression-lh expr)) (car (expression-plist expr)) n))
             (rh (loop '() (term-list-l (expression-rh expr)) (cdr (expression-plist expr)) (quotient n (apply * (flatten (car (expression-plist expr))))))))
        (make-expression (expression-type expr) (apply terms lh) (apply terms rh) (expression-bindings expr) '())
      )
    )
  )
)


(define extract-expression
  (lambda (expr)
    (letrec
      ((f
         (lambda (out in)
           (if (eqv? in '())
             out
             (let ((term (car in)))
               (cond
                 ((term-const? term) (f (cons (if (term-const-binding term) (cons 'C (term-const-binding term)) 'C) out) (cdr in)))
                 ((term-var? term) (f (cons (if (term-var-binding term) (cons 'v (term-var-binding term)) 'V) out) (cdr in)))
                 ((term-op? term) (f (append (list (cons (term-op-op term) (f '() (term-op-operands term)))) out) (cdr in)))
                 ((permutation? term) (f (append (cons 'P (list (f '() (permutation-body term)))) out) (cdr in)))
                 ((list? term) (f (append (f '() (list (car term))) (f '() (cdr term)) out) (cdr in)))
               )
             )
           )
         )
       ))
      (append (f '() (term-list-l (expression-lh expr))) (list (expr-type-type (expression-type expr))) (f '() (term-list-l (expression-rh expr))))
    )
  )
)

(define generate-constant
  (lambda (c)
    (assert (term-const? c) "expected constant term as argument to generate-constant")
    (let* ((r (term-const-range c))
           (rmin (if r (car r) (car default-constant-range)))
           (rmax (if r (cdr r) (cdr default-constant-range))))
      (cons
        (+ rmin (random (- rmax rmin)))
        ((lambda (b) (if b (bound-term-ident b) #f)) (term-const-binding c))
      )
    )
  )
)

(define generate-variable
  (lambda (v)
    (assert (term-var? v) "expected variable term as argument to generate-variable")
    (cons
      (if (term-var-range v)
        (choose-from-list (term-var-range v))
        (choose-from-list default-variable-range)
      )
      ((lambda (b) (if b (bound-term-ident b) #f)) (term-var-binding v))
    )
  )
)

(define generate
  (lambda (expr)
    (assert (expression? expr) "expected expression as argument to generate")
    (letrec
      ((gen
         (lambda (tlist vals)
           (if (eqv? tlist '())
             vals
             (let ((term (car tlist)))
               (cond
                 ((term-const? term)
                  (gen (cdr tlist) (cons (generate-constant term) vals)))
                 ((term-var? term)
                  (gen (cdr tlist) (cons (generate-variable term) vals)))
                 ((term-op? term)
                  (gen (cdr tlist) (cons (cons (term-op-op term) (gen (term-op-operands term) '())) vals)))
                 (else (gen (cdr tlist) (cons '? vals)))
               )
             )
           )
         )
      ))
      (make-instance expr (cons (gen (term-list-l (expression-rh expr)) '()) (gen (term-list-l (expression-lh expr)) '())) '())
    )
  )
)




;(define new
;  (lambda (expr #!optional count #!rest parameters)
;    (let ((c (if (number? count) count 1)))
;      (let loop ((n 0) (ies '()))
;        (if (equal? n c)
;          ies
;          (let* (
;                 (raw-expr (resolve-permutations expr n))
;                 (gen-expr (gen raw-expr))
;                )
;            (loop
;              (+ n 1)
;              (cons (make-instance raw-expr gen-expr (map (lambda (name proc) (cons name (proc gen-expr))))) ies)
;            )
;          )
;        )
;      )
;    )
;  )
;)
;
