(declare (unit defs))

(define-record num-type type)
(define-record expr-type type)
(define-record bound-term ident)

(define-record term-const binding range)
(define-record term-var binding)
(define-record term-op op operands)

(define-record term-list l)
(define-record expr type lh rh)

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
    (begin
      (aql-assert (num-type? type) "expected type as first argument to constant")
      (if binding
        (aql-assert (bound-term? binding) "expected binding or #f as second argument to constant")
      )
      (if range
        (aql-assert (or (pair? range) (list? range)) "expected pair or list as third argument to constant")
      )
      (make-term-const binding range)
    )
  )
)

(define bind
  (lambda (ident)
    (begin
      (aql-assert (symbol? ident) "expected symbol as argument to bind")
      (make-bound-term ident)
    )
  )
)

(define variable
  (lambda (#!optional binding)
    (begin
      (if binding
        (aql-assert (bound-term? binding) "expected binding as argument to variable")
      )
      (make-term-var binding)
    )
  )
)

(define integer (make-num-type 'integer))
(define rational (make-num-type 'rational))
(define decimal (make-num-type 'decimal))

(define term-object?
  (lambda (t)
    (or (term-const? t) (term-var? t) (term-op? t))
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
    (begin
      (aql-assert (valid-tlist? tlist) "expected series of term objects as argument to terms")
      (make-term-list tlist)
    )
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

(define expression
  (lambda (type lh rh)
    (begin
      (aql-assert (expr-type? type) "expected expression type as first argument to expression")
      (aql-assert (and (term-list? lh) (term-list? rh)) "expected term list as second and third argumnet to expression")
      (make-expr type lh rh)
    )
  )
)


