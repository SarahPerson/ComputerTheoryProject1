;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; STARTER DEFINITIONS FOR FINITE AUTOMATA ;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A structure type for finite automata
(defstruct (finite-automaton)
  "A Finite Automaton."
  ;; list of states
  (states nil :type list)

  ;; list of alphabet symbols
  (alphabet nil :type list)

  ;; edge list,
  ;; each element is a list (predecessor-state input-symbol successor-state)
  (edges nil :type list)

  ;; start state
  start

  ;; list of accept states
  (accept nil :type list))

(defun make-fa (edges start accept)
  "Convenience constructor for finite automata"
  (let ((state-hash (make-hash-table :test #'equal))
        (alphabet-hash (make-hash-table :test #'equal)))
    ;; Prime state set
    (setf (gethash start state-hash) t)
    (dolist (a accept)
      (setf (gethash a state-hash) t))
    ;; Collect states and alphabet from edges
    (loop for (q0 e q1) in edges
       do (setf (gethash q0 state-hash) t
                (gethash e alphabet-hash) t
                (gethash q1 state-hash) t))
    ;; Result
    (make-finite-automaton
     :states (loop for k being the hash-key in state-hash collect k)
     :alphabet (loop for k being the hash-key in alphabet-hash collect k)
     :start start
     :accept accept
     :edges edges)))

(defun dot-symbol (thing)
  "Pretty-print greek letters for Graphviz output"
  (case thing
    (:alpha "&alpha;")
    (:beta "&beta;")
    (:gamma "&gamma;")
    (:delta "&delta;")
    (:epsilon "&epsilon;")
    (:zeta "&zeta;")
    (:eta "&eta;")
    (:theta "&theta;")
    (:iota "&iota;")
    (:kappa "&kappa;")
    (:lambda "&lambda;")
    (:mu "&mu;")
    (:nu "&nu;")
    (:xi "&xi;")
    (:omicron "&omicron;")
    (:pi "&pi;")
    (:rho "&rho;")
    (:sigma "&sigma;")
    (:tau "&tau;")
    (:upsilon "&upsilon;")
    (:phi "&phi;")
    (:chi "&chi;")
    (:omega "&omega;")
    (t thing)))

;; Example:
;;
;; (fa-dot (make-fa '((q-even 0 q-even)
;;                    (q-even 1 q-odd)
;;                    (q-odd 1 q-even)
;;                    (q-odd 0 q-odd))
;;                  'q-even
;;                  '(q-odd))
;;         "/tmp/cs561-project-1-example.dot")
(defun fa-dot (fa place)
  "Output a Graphviz dot file for finite automata"
  (let ((hash (make-hash-table :test #'equal)))
    ;; number the states
    (loop for i from 0
       for q in (finite-automaton-states fa)
       do (setf (gethash q hash) i))
    (labels ((state-number (state)
               (gethash state hash))
             (helper (stream)
               ;; output
               (format stream "~&digraph { ~%")
               ;; state labels
               (format stream "~:{~&  ~A[label=\"~A\"];~}"
                       (map 'list (lambda (state)
                                    (list (state-number state)
                                          state))
                            (finite-automaton-states fa)))
               ;; start shape
               (format stream "~&  start[shape=none];")
               (format stream "~&  start -> ~A;"
                       (state-number (finite-automaton-start fa)))
               ;; accept state
               (format stream "~:{~&  ~A [ shape=~A ];~}"
                       (map 'list (lambda (q)
                                    (list (state-number q) "doublecircle"))
                            (finite-automaton-accept fa)))
               ;; edges
               (loop for (q0 e q1) in (finite-automaton-edges fa)
                  do (format stream "~&  ~A -> ~A [fontsize=~D,label=\"~A\"];~%"
                             (state-number q0)
                             (state-number q1)
                             12 (dot-symbol e)))
               ;; end
               (format stream "~&}~%")))
      (cond
        ((streamp  place)
         (helper place))
        ((eq place t)
         (helper *standard-output*))
        ((or (stringp place)
             (pathnamep place))
         (with-open-file (stream place
                                 :direction :output
                                 :if-exists :supersede
                                 :if-does-not-exist :create)
         (helper stream)))
        (t (error "Unrecognized output type: ~A" place))))))

;; SBCL-specific function to generate a PDF of the FA
;;
;; Example:
;;
;; (fa-pdf (make-fa '((q-even 0 q-even)
;;                    (q-even 1 q-odd)
;;                    (q-odd 1 q-even)
;;                    (q-odd 0 q-odd))
;;                  'q-even
;;                  '(q-odd))
;;         "/tmp/cs561-project-1-example.pdf"(list edges end))
#+sbcl
(defun fa-pdf (fa pathname)
  (with-input-from-string (input (with-output-to-string (stream)
                                     (fa-dot fa stream)))
    (with-open-file (output pathname :direction :output :if-exists :supersede)
      (sb-ext:run-program "dot" (list "-Tpdf")
                          :search t
                          :wait t
                          :input input
                          :output output))))



(defun state-predicate-atom (a b)
  "Predicate to order states, atom case."
  (etypecase a
    ((or symbol string)
     (etypecase b
       ((or symbol string)
        (string-lessp a b))
       (number nil)))
    (number
     (etypecase b
       ((or symbol string)
        t)
       (number (<= a b))))))

(defun state-predicate (a b)
  "Predicate to order states."
  (etypecase a
    (atom (etypecase b
            (atom (state-predicate-atom a b))
            (list t)))
    (cons (etypecase b
            (atom nil)
            (cons (if (equal (car a) (car b))
                      (state-predicate (cdr a)
                                       (cdr b))
                      (state-predicate (car a)
                                       (car b))))))))

(defun newstate ()
  "Construct a unique state for a finite automaton."
  (gensym "q-"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; COMPLETE THE FUNCTIONS BELOW ;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun TODO (thing)
  (error "Unimplemented: ~A" thing))

;; Convert a regular expression to a nondeterministic finite automaton
;;
;; The following are examples of possible regular expression arguments to this function:
;;
;; - (:concatenation a b c)
;; - (:union a b c)
;; - (:kleene-closure a)
;; - (:concatenation (:union a b) (:kleene-closure c))

(defun regex->nfa (regex)
 (let ((state-counter 0))
   (labels ((rec (x regex)
             (destructuring-bind (edges start)
               (cond 
                    ((not (listp regex))
                     (push (list start regex (incf state-counter)) edges) (list edges state-counter)) 
                    (t
                     (ecase (car regex)
                      (:concatenation
                       (reduce #'rec (cdr regex)
                               :initial-value (list edges start)))
                      (:union
                       (let ((end ( incf state-counter)))
                         (loop for s in (cdr regex)
                             do(destructuring-bind (newedges state) (rec (list edges start) s)
                                 (push (list state :epsilon end) newedges   )
                                 (setq edges newedges)
                             )                                             
                         )
                         (list edges end)
                       )
                       )
                      
                      (:kleene-closure 
                       (let ((newstate (incf state-counter))
                             (endstate nil))
                         (destructuring-bind (newedges end) (rec (list edges newstate) (cadr regex))
                           
                           
                           (push (list start :epsilon newstate) newedges)
                           (push (list start :epsilon end) newedges)
                           (push (list end :epsilon newstate) newedges)
                          
                           
                           (setq edges newedges) 
                           (setq endstate end)

                         )
                         (list edges endstate)
                        )
                       
                       )
                      )
                      )))))
    (let* ((start (newstate)))
         (destructuring-bind (edges accept)
             (rec (list nil start) regex)
           (make-fa edges start (list accept)))))))

;; Convert a nondeterministic finite automaton to a deterministic
;; finite automaton
;;
(defun nfa->dfa (nfa)
  (let ((Q nil))
    (labels (( visit-state(e u)
               (labels ((visit-symbol (e sigma)
                          ;;(print e)
                          ;;(print sigma)
                          ;;(print  u)
                          (let ((uPrime (move-e-closure nfa  u sigma)))
                            ;;(print  sigma)
                            (if uPrime
                                (if (not (set-member e (list u sigma uPrime ) ))
                                    (visit-state (push (list u sigma uPrime )  e) uPrime)
                                  )
                               
                              e
                            )
                            )
                          )) 
               ;;(print u)
               ;;(print Q)
               (if (set-member Q  u )
                   e
                 (progn 
                   ;;(print Q)
                  
                   (setf Q (union (list u)  Q))
                   (reduce #'visit-symbol  (remove :epsilon (finite-automaton-alphabet nfa))
                           :initial-value  e )
                   ;;(print Q)
                   )
                 
                 )
               )
               ))
      
      
    (let ((newq0 (e-closure nfa (list (finite-automaton-start nfa)) nil))
          (E nil)
          (FPrime nil))
      ;; visit state
      (setf E (visit-state  nil  newq0))
      
      ;; create new F
      (loop for s in Q
            do (if (set-member (finite-automaton-accept nfa) s)
                   (push s FPrime)
                   )

       )

      (make-fa E newq0 FPrime)
      
      )
     
     
     
    ) 
    )
  )

(defun set-member (set item)
  (if (not set)
    nil
    (if (equal item (car set))
        t
        (set-member (cdr set) item) 
    )
  )
)



(defun sample-nfa ()
  (make-fa '((q0 0 q0)
             (q0 :epsilon q1)
             (q1 1 q1)
             (q1 :epsilon q2)
             (q2 2 q2))
           'q0
           '(q2))
  )

(defun e-closure (nfa S C)
  (let ((edges (finite-automaton-edges nfa)))
    
    ;; create the visit function
    (labels ((visit (c q)
               (cond
                ;;base case state q already in closure
                ((member q c)
                 c)
                ;; get all reachable states with e
                (t
                 (let ((p nil))
                   (setq c (union c (list q)))
                   (loop for (q0 edge q1) in edges
                         if (and (equal q0 q) (equal edge :epsilon))
                         do (setq p (union p (list q1))))
                  
                 
                ;; recursively call e closure
                (e-closure nfa p  c))))))
  (reduce #'visit S
          :initial-value  C ))))


(defun move-e-closure (nfa S sigma)
  (let ((edges (finite-automaton-edges nfa))
        (initialSet (e-closure nfa S nil)))
    
    ;; create the visit function
    (labels ((visit (c q)
               (let ((states nil))
                 (loop for (q0 edge q1) in edges
                       if(and (equal q0 q) (equal edge sigma))
                       do (setq states (union states (list q1)))
                 )
                 (e-closure nfa states c)
                 )))
               
  (reduce #'visit initialSet
          :initial-value nil  ))))


;; Compute the intersection between the arguments
(defun dfa-intersection (dfa-0 dfa-1)
  (let ((states (make-hash-table :test #'equal))
        (edges))
    (labels ((visit (q)
               (unless (gethash q states)
                 (setf (gethash q states) t)
                 (destructuring-bind (q0 q1) q
                   (TODO 'dfa-intersection)))))
      (let ((s (list (finite-automaton-start dfa-0)
                     (finite-automaton-start dfa-1))))
        (visit s)
        (TODO 'dfa-intersection)))))


;; Minimize the states in the dfa
(defun dfa-minimize (dfa)
  (TODO 'dfa-minimize))

;; sample nfa



;;;;;;;;;;;;;;;;;;;;;;
;;;; EXTRA CREDIT ;;;;
;;;;;;;;;;;;;;;;;;;;;;

;; ;; Return the complement of FA
;; (defun fa-complement (fa ))

;; ;; Test whether two FA are equivalent
;; (defun fa-equivalent (fa-0 fa-1))

;; ;; Test whether FA-0 is subseteq of FA-1
;; (defun fa-subseteq (fa-0 fa-1))
