#lang rosette

(require rosette/lib/synthax)

; select the child with key in obj
(define (child obj key)
  (let ([x (assoc key obj)]) (if (not x) null (cdr x))))

; select the object at index in obj
(define (index obj idx)
  (cond
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

; streq compares two strings for equality
(define (syntEq str1 str2)
  (cond
    [(|| (empty? str1) (empty? str2))
    #f
    ]
    [else (equal? str1 str2)]
    )
  )


(provide child)
(provide index)
(provide descendant)
(provide syntEq)