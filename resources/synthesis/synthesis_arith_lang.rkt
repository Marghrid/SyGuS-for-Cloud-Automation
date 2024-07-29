#lang rosette

(require rosette/lib/synthax)


; select the object at index in obj
(define (index obj idx)
  (cond
    [(list? obj) (if (> (length obj) idx) (list-ref obj idx) (list))]
    [else null]
    )
  )

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


(provide index)
(provide syntEq)
(provide syntAdd)