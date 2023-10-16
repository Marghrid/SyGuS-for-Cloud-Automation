#lang rosette

(require rosette/lib/synthax)

; check if an object is a dict
(define (is_synt_dict obj)
  (and (dict? obj)
       (andmap
        (lambda (el) (and (pair? el) (string? (car el))))
        obj)
       )
  )

; select the child with key in obj
(define (child obj key)
  (let ([x (assoc key obj)]) (if (not x) null (cdr x))))

; select the object at index in obj
(define (index obj idx)
  (cond
    [(is_synt_dict obj) null]
    [(list? obj) (if (> (length obj) idx) (list-ref obj idx) null)]
    [else null]
    )
  )

; descendant selects all descendants with key key
(define (descendant obj key)
  (cond
    [(list? obj)
     (flatten
      (map
       (lambda (x)
         (if (pair? x)
             (if (equal? (car x) key) (list (cdr x)) (descendant (cdr x) key))
             (descendant x key)))
       obj))]
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


(provide child)
(provide index)
(provide descendant)
(provide syntEq)
(provide syntAdd)