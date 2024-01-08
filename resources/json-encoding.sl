(set-logic ALL)
(set-option :produce-models true)

; recursive datatypes declared together
(declare-datatypes ((Json 0) (JsonDict 0) (JsonList 0)) ((
    (jS (sval String))
    (jI (ival Int))
    (jB (bval Bool))
    (jL (lval JsonList))
    (jD (dval JsonDict))
    (jNull)
  )(
    (j_nil_dict)
    (dict_cons (key String) (val Json) (jdtail JsonDict))
  )(
    (j_nil_list)
    (list_cons   (j_head Json) (j_tail JsonList))
  )
  ))


(define-fun-rec find_key ((keyV String) (dict JsonDict)) Json
  (match dict
  (
    (j_nil_dict jNull)
    ((dict_cons _key _val rest) (ite (= _key keyV) _val (find_key keyV rest)))
  ))
)

(define-fun get_val_dict ((x Json) (keyV String)) Json
  (match x
    (
      ((jS x) jNull)
      ((jI x) jNull)
      ((jB x) jNull)
      ((jL x) jNull)
      ((jD dict) (find_key keyV dict))
      (jNull jNull)
    ))
)

(define-fun-rec nth_list ((li JsonList) (n Int)) Json
  (ite (< n 0)
    jNull
      (match li ((j_nil_list jNull) ((list_cons h r) (ite (= n 0) h (nth_list r (- n 1))))))
  )
)

(define-fun-rec list_length ((li JsonList)) Int
  (match li (
        (j_nil_list 0)
        ((list_cons h t) (+ 1 (list_length t)))
  ))
)

(define-fun-rec dict_length ((dict JsonDict)) Int
  (match dict (
        (j_nil_dict 0)
        ((dict_cons k v t) (+ 1 (dict_length t)))
  ))
)

(define-fun length ((jx Json)) Int
  (match jx (
      ((jS x) 1)
      ((jI x) 1)
      ((jB x) 1)
      ((jL li) (list_length li))
      ((jD dict) (dict_length dict))
      (jNull 0)
    ))
)

(define-fun empty ((jx Json)) Bool
  (match jx
    (
      ((jS x) true)
      ((jI x) true)
      ((jB x) true)
      ((jL li) (= li j_nil_list))
      ((jD dict) (= dict j_nil_dict))
      (jNull false)
    ))
)

(define-fun-rec concat_list ((l JsonList) (r JsonList)) JsonList
  (match l
  (
    (j_nil_list r)
    ((list_cons h t) (list_cons h (concat_list t r)))
  ))
)

(define-fun get_idx_list ((x Json) (idx Int)) Json
  (match x
    (
      ((jS x) jNull)
      ((jI x) jNull)
      ((jB x) jNull)
      ((jL li) (nth_list li idx))
      ((jD dict) jNull)
      (jNull jNull)
    ))
)

(define-funs-rec (
  (get_descendants_named ((x Json) (keyV String)) Json)
  (collect_descendants_dict ((xd JsonDict) (keyV String) (accum JsonList)) JsonList)
  )
  ((match x
    (
      (jNull jNull)
      ((jS x) jNull)
      ((jI x) jNull)
      ((jB x) jNull)
      ((jL li) jNull)
      ((jD dict) (let
        ((res (find_key keyV dict)))
        (ite (= res jNull)
          (jL (collect_descendants_dict dict keyV j_nil_list))
          res
        )
      ))))
    (match xd
      ((j_nil_dict accum)
      ((dict_cons _key _val rest)
        (let ((res (get_descendants_named _val keyV)))
          (match res
            (
              (jNull (collect_descendants_dict rest keyV accum))
              ((jS s) (collect_descendants_dict rest keyV (list_cons (jS s) accum)))
              ((jI e) (collect_descendants_dict rest keyV (list_cons (jI e) accum)))
              ((jB e) (collect_descendants_dict rest keyV (list_cons (jB e) accum)))
              ((jD e) (collect_descendants_dict rest keyV (list_cons (jD e) accum)))
              ((jL l) (collect_descendants_dict rest keyV (concat_list l accum)))
            )
          )
        )
      ))
    )
  )
)

; Example sygus synthesis problem for JSON.

; (declare-const x Json)
; (assert (= (get_val_dict x "key1") (jS "example")))
; (assert (= (get_val_dict x "key2") (jS "example2")))
; (assert (= (get_val_dict x "key4") jNull))
; (assert (= (get_idx_list (get_val_dict x "key3") 2) (jS "example3")))
; (assert (=  (get_descendants_named x "key4") (jL (list_cons (jS "ok0") (list_cons (jS "ok1") j_nil_list)))))
; (check-sat) ; interestingly prints unknown for satisfiability but finds a solution
; (get-model)

(synth-fun json-selector ((x Json)) Json
  ;;Non terminals of the grammar
  ((SynthJ Json) (SySK String) (SySV String) (SynthInt Int) (SynthBool Bool))
  ;;Define the grammar
  (
    (SynthJ Json (
      (get_idx_list x SynthInt)
      (get_idx_list SynthJ SynthInt)
      (get_val_dict SynthJ SySK)
      (get_descendants_named SynthJ SySK)
    ))
    (SySK String ("key1" "key2" "key3"))
    (SySV String ("example" "example2" "example3"))
    (SynthInt Int (
      0 1 2
      (length SynthJ)
    ))
    (SynthBool Bool (
      (empty SynthJ)
      (not SynthBool)
      (= SynthJ (jS SySV))
    ))
  )
)

; Samples are lists of arguments
(define-const sample0 Json
  (jL (list_cons (jD (dict_cons "key1" (jS "example")
        (dict_cons "key2"  (jL
          (list_cons (jS "")
            (list_cons (jS "") (list_cons (jS "example3") j_nil_list))
          ))
          (dict_cons "key3" (jS "example2") j_nil_dict)
        )
      )) j_nil_list))
)

(constraint (= (json-selector sample0) (jS "example2")))

(check-synth)