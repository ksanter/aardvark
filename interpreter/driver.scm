(declare (uses defs))

(if
  (equal?
    (length (argv))
    1
  )
  (begin
    (print "(no input files)")
    (exit)
  )
)

(define parse
  (lambda (fname)
    (try
      (lambda ()
        (begin
          (load fname)
        )
      )
    )
  )
)

(define show-repl #f)
(define file-list
  (if
    (string=?
      (cadr (argv))
      "-i"
    )
    (begin
      (set! show-repl #t)
      (cddr (argv))
    )
    (cdr (argv))
  )
)

(for-each parse file-list)

(if show-repl (repl))
