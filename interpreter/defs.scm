(declare (unit defs))

(define-record num-type type)
(define-record expr-type type)
(define-record bound-term ident)

(define-record term-const binding range)
(define-record term-var binding)
(define-record term-op op operands)
(define-record permutation forms body type)

(define-record term-list l)
(define-record expression type lh rh bindings plist)

(define-record instance expr vals properties)

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
  (lambda (#!optional binding)
    (if binding
      (aql-assert (bound-term? binding) "expected binding as argument to variable")
    )
    (make-term-var binding)
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
    (make-term-op '- opers)
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
                                       (if (eqv? subpl '())
                                         (cons (list (length (permutation-forms term))) p)
                                         (cons (cons (length (permutation-forms term)) subpl) p)
                                       )
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
    (letrec ((flatten
               (lambda (l)
                 (cond
                   ((null? l) '())
                   ((pair? l) (append (flatten (car l)) (flatten (cdr l))))
                   (else (list l))
                 )
               )
            ))
      (let ((flat (flatten (expression-plist expr))))
        (apply * flat)
      )
    )
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
      (append (permutation-list lh) (permutation-list rh))
    )
  )
)

(define permute-type-maker
  (lambda (type)
    (lambda (#!rest forms)
      (lambda (#!rest body)
        (aql-assert (valid-tlist? body) "expect series of term objects as body of permutation")
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
;    (let loop ((tlist (append (expression-lh expr) (expression-rh expr))))





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
