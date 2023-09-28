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
             (if (eq? (car x) key) (list (cdr x)) (descendant (cdr x) key))
             (descendant x key)))
       obj))]
    [else null]
    )
  )


(provide child)
(provide index)
(provide descendant)