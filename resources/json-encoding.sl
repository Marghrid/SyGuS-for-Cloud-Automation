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
  ((SynthJ Json (
    x
    (get_val_dict SynthJ SySK)
    (get_descendants_named SynthJ SySK)
    (get_idx_list SynthJ SynthInt)
    ))
    (SySK String ("key1" "key2" "key3"))
    (SySV String ("example" "example2" "example3"))
    (SynthInt Int (
      0 1 2
      (length SynthJ)
    ))
    (SynthBool Bool (
      (empty SynthJ)
      (= SynthJ (jS SySV))
      (not SynthBool)
      ))
  ))

(constraint (= (json-selector
  (jD (dict_cons "key1" (jS "example")
        (dict_cons "key2"  (jL 
          (list_cons (jS "")
            (list_cons (jS "")
              (list_cons (jS "example3") j_nil_list)
            )
          ))
          (dict_cons "key3" (jS "example2") j_nil_dict)
        )
      ))
    )
  (jS "example2")))

(check-synth)