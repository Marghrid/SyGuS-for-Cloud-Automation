#lang rosette

(require rosette/lib/synthax)

(struct KV (K V) #:transparent)

; check if an object is a dict
(define (is_synt_dict obj)
  (and (dict? obj)
       (andmap
        (lambda (el) (and (KV? el) (string? (KV-K el))))
        obj)
       )
  )

; select the child with key in obj
(define (child obj key)
  (if (list? obj)
      (let ([maybe-child (findf (lambda (arg) (and (KV? arg) (equal? (KV-K arg) key))) obj)])
        (if maybe-child (KV-V maybe-child) null))
      null))

; select the object at index in obj
(define (index obj idx)
  (cond
    [(is_synt_dict obj) null]
    [(list? obj) (if (> (length obj) idx) (list-ref obj idx) (list))]
    [else null]
    )
  )

; descendant selects all descendants with key key
(define (descendant obj key)
  (append* (cond
             [(list? obj)
              (append
               (map
                (lambda (x)
                  (if (KV? x)
                      (if
                       (equal? (KV-K x) key)
                       (list (KV-V x))
                       (descendant (KV-V x) key))
                      (descendant x key)))
                obj))]
             [else (list)]
             )))


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
(provide KV)