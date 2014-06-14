(declare (unit defs))

(use extras)

(define-record num-type type)
(define-record eq-type type)
(define-record bound-term ident)

(define-record term-const binding range)
(define-record term-var binding range)
(define-record term-op op operands)
(define-record permutation forms body type)

(define-record term-list l)
(define-record equation type lh rh)

(define-record question obj fns properties)

;(define-record instance expr vals properties)

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

(define expr-object?
  (lambda (t)
    (or (term-list? t) (equation? t))
  )
)

(define valid-tlist?
  (lambda (tlist)
    (cond 
      ((eqv? tlist '()) #t)
      ((not (list? tlist)) #f)
      ((term-object? (car tlist)) (valid-tlist? (cdr tlist)))
      (else #f)
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

(define et-equality (make-eq-type '=))
(define et-inequality-gt (make-eq-type '>))
(define et-inequality-lt (make-eq-type '<))
(define et-inequality-gte (make-eq-type '>=))
(define et-inequality-lte (make-eq-type '<=))

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

(define term-list-pnum
  (lambda (t)
    (apply * (flatten (extract-bindings t)))
  )
)

(define terms
  (lambda (#!rest tlist)
    (aql-assert (valid-tlist? tlist) "expected series of term objects as argument to terms")
    (make-term-list tlist)
  )
)

(define equation
  (lambda (type lh rh)
    (aql-assert (eq-type? type) "expected equality type type as first argument to equation")
    (aql-assert (and (term-list? lh) (term-list? rh)) "expected term list as second and third argument to equation")
    (make-equation
      type
      lh
      rh
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
  (lambda (obj n)
    (letrec
       ((loop
         (lambda (res tlist pl i)
           (if (eqv? tlist '())
             (reverse res)
             (let ((term (car tlist)))
               (cond
                 ((permutation? term) (let
                                        ((t (list-ref (permutation-forms term) (modulo i (caar pl))))
                                         (r (loop '() (permutation-body term) (cdar pl) (quotient i (caar pl)))))
                                        (loop
                                          (cons
                                            (if (procedure? t)
                                              (let ((b (apply t r)))
                                                (assert (or (term-object? b) (valid-tlist? b)) "expected permutation body to resolve to list of terms")
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
;                                      (quotient i (let ((flat (flatten (car pl)))) (if (eqv? flat '()) 1 (apply * flat))))
                                      (quotient i (apply * (flatten (car pl))))
                                    )
                                  ))
                 (else (loop (cons term res) (cdr tlist) pl i))
               )
             )
           )
         )
       ))
       (cond
         ((equation? obj)
          (let* ((lh-orig (equation-lh obj))
                 (rh-orig (equation-rh obj))
                 (lh-plist (permutation-list lh-orig))
                 (lh (loop '() (term-list-l lh-orig) lh-plist n))
                 (rh (loop '() (term-list-l rh-orig) (permutation-list rh-orig) (quotient n (apply * (flatten lh-plist))))))
            (make-equation (equation-type obj) (apply terms lh) (apply terms rh))
          ))
         ((term-list? obj)
          (apply terms (loop '() (term-list-l obj) (permutation-list obj) n)))
         (else (except "expected equation or term list as argument to resolve-permutations"))
       )
    )
  )
)

(define extract-output
  (lambda (obj)
    (letrec
      ((f
         (lambda (out in)
           (if (eqv? in '())
             out
             (let ((term (car in)))
               (cond
                 ((term-const? term) (f (cons (if (term-const-binding term) (cons 'C (term-const-binding term)) 'C) out) (cdr in)))
                 ((term-var? term) (f (cons (if (term-var-binding term) (cons 'v (term-var-binding term)) 'V) out) (cdr in)))
;                 ((term-op? term) (f (append (list (cons (term-op-op term) (f '() (term-op-operands term)))) out) (cdr in)))
                 ((term-op? term) (f (cons (cons (term-op-op term) (f '() (term-op-operands term))) out) (cdr in)))
                 ((permutation? term) (f (cons (let ((sub (f '() (permutation-body term)))) (if (eqv? sub '()) 'P (cons 'P sub))) out) (cdr in)))
;                 ((permutation? term) (f (append (let ((sub (list (f '() (permutation-body term))))) (if (eqv? sub '()) (cons 'P (list sub)) (list 'P))) out) (cdr in)))
                 ((list? term) (f (append (f '() (list (car term))) (f '() (cdr term)) out) (cdr in)))
               )
             )
           )
         )
       ))
      (cond
        ((equation? obj)
         (cons (eq-type-type (equation-type obj)) (cons (f '() (term-list-l (equation-lh obj))) (f '() (term-list-l (equation-rh obj))))))
        ((term-list? obj)
         (f '() (term-list-l obj)))
        (else (except "expected equation or term list as argument to extract-raw"))
      )
    )
  )
)

(define question
  (lambda (obj #!rest props)
    (assert (expr-object? obj) "expected expression object as first argument to question")
    (assert (list-true? (map pair? props)) "expected series of pairs as second+ argument to question")
    (make-question obj props)
  )
)

;(define instance
;  (lambda (obj vals)
;    (assert (expr-object? obj) "expected expression object as first argument to instance")
;    (assert (list? vals) "expected list of value pairs as first argument to instance")
;    (make-instance obj (value-list vals))
;  )
;)

(define generate
  (lambda (tlist)
    (if (eqv? tlist '())
      '()
      (let ((term (car tlist)))
        (cons
          (cond
            ((term-const? term) (generate-constant term))
            ((term-var? term) (generate-variable term))
            ((term-op? term) (cons (term-op-op term) (generate (term-op-operands term))))
          )
          (generate (cdr tlist))
        )
      )
    )
  )
)

(define value-list
  (lambda (vals)
    (if (eqv? vals '())
      '()
      (cond
        ((and (pair? (car vals)) (not (list? (car vals)))) (cons (car vals) (value-list (cdr vals))))
        ((list? (car vals)) (append (value-list (car vals)) (value-list (cdr vals))))
        (else (value-list (cdr vals)))
      )
    )
  )
)

(define vl-get
  (lambda (b vlist)
    (if (eqv? vlist '())
      #f
      (if (eqv? (cdar vlist) b)
        (caar vlist)
        (vl-get b (cdr vlist))
      )
    )
  )
)

;(define resolve-bindings
;  (lambda (tlist fns)
;    (letrec
;      ((gen-vals
;         (lambda (in)
;           (if (eqv? 
;           (cons (cond
;                   ((
;       
;       (res-single
;         (lambda (out in b fn vals)
;
;    (let loop ((out '()) (in '()))
;    )
;  )
;)
;

;(define ask
;  (lambda (q #!optional (n 1))
;    (assert (question? q) "expected question as first argument to ask")
;    (assert (and (integer? n) (> n 0)) "expected number as second argument to ask")
;    (letrec
;      ((f
;         (lambda (i out in)
;         )
;       )
;       (loop
;         (lambda (i)
;         )
;       ))
;      (cons (cons 'raw (extract-output (question-obj q))) (loop n))
;    )
;            out
;        (let
;          ((r (resolve-permutations q i))
;           (
;  )
;)

(define generate-constant
  (lambda (c)
    (assert (term-const? c) "expected constant term as argument to generate-constant")
    (let ((r (term-const-range c))
          (f (lambda (b) (if b (bound-term-ident b) #f))))
      (if (or (eqv? r #f) (pair? r))
        (let
          ((rmin (if r (car r) (car default-constant-range)))
           (rmax (if r (cdr r) (cdr default-constant-range))))
          (cons
            (+ rmin (random (- rmax rmin)))
            (f (term-const-binding c))
          )
        )
        (cond
          ((number? r) (cons r (f (term-const-binding c))))
          ((list? r) (cons (choose-from-list r) (f (term-const-binding c))))
        )
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

;(define generate
;  (lambda (expr)
;    (assert (expression? expr) "expected expression as argument to generate")
;    (letrec
;      ((gen
;         (lambda (tlist vals)
;           (if (eqv? tlist '())
;             vals
;             (let ((term (car tlist)))
;               (cond
;                 ((term-const? term)
;                  (gen (cdr tlist) (cons (generate-constant term) vals)))
;                 ((term-var? term)
;                  (gen (cdr tlist) (cons (generate-variable term) vals)))
;                 ((term-op? term)
;                  (gen (cdr tlist) (cons (cons (term-op-op term) (gen (term-op-operands term) '())) vals)))
;                 (else (gen (cdr tlist) (cons '? vals)))
;               )
;             )
;           )
;         )
;      ))
;      (make-instance expr (cons (expr-type-type (expression-type expr)) (cons (gen (term-list-l (expression-rh expr)) '()) (gen (term-list-l (expression-lh expr)) '()))) '())
;    )
;  )
;)
;
;(define extract-instance
;  (lambda (i)
;    (let loop ((out '()) (in (instance-vals i)))
;      (print in)
;      (if (eqv? in '())
;        out
;        (if (pair? in)
;          (let ((term (car in)))
;            (if (pair? term)
;              (if (list? term)
;                (loop (cons (loop '() (car term)) out) (cdr in))
;                (loop (cons (car term) out) (cdr in))
;              )
;              (loop (cons term out) (cdr in))
;            )
;          )
;          (cons in out)
;        )
;      )
;    )
;  )
;)
;


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
