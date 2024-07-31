#lang rosette

(require rosette/lib/synthax)

; syntEq compares two objects for equality
(define (syntEq arg1 arg2)
  (cond
    [(and (and (string? arg1) (string? arg2))
          (or (empty? arg1) (empty? arg2)))
     #f
     ]
    [else (equal? arg1 arg2)]
    )
  )

; syntAdd concatenates two strings or adds the value of two numerical values.
(define (syntAdd arg1 arg2)
  (cond
    [(and (string? arg1) (string? arg2))
     (string-append arg1 arg2)
     ]
    [else (+ arg1 arg2)]
    )
  )

(define (power x n)
  (cond
  [(< n 0) 0]
  [(zero? n) 1]
  [else (* x (power x (- n 1)))]
    )
  )

(provide syntEq)
(provide syntAdd)
(provide power)
