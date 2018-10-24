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
             (destructuring-bind (edges start) x
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
               
               (setq u (sort-state u))
               (if (set-member Q  u )
                   e
                 (progn 
                   (setf Q (union (list u)  Q))
                   (reduce #'visit-symbol  (remove :epsilon (finite-automaton-alphabet nfa))
                           :initial-value  e ))))))
      
      
    (let ((newq0 (e-closure nfa (list (finite-automaton-start nfa)) nil))
          (E nil)
          (FPrime nil))
      ;; visit state
      (setf E (visit-state  nil  newq0))
      
      ;; create new F
      (loop for s in Q
            do (loop for f in (finite-automaton-accept nfa)
                  do (if (set-member s f)
                         (push s FPrime)
                       )))

      (make-fa E newq0 FPrime)
      
      ))))

(defun sort-state (u)
  (sort u #'state-predicate)) 

(defun set-member (set item)
  (if (not set)
    nil
    (if (equal item (car set))
        t
        (set-member (cdr set) item) 
    )
  )
)


;;;;;;;;;;;; Test NFA's ;;;;;;;;;;;;;;;;
(defun sample-nfa ()
  (make-fa '((q0 0 q0)
             (q0 :epsilon q1)
             (q1 1 q1)
             (q1 :epsilon q2)
             (q2 2 q2))
           'q0
           '(q2))
  )

(defun sample-nfa-2()
  (make-fa '((q0 :epsilon q2)
             (q0 b q1)
             (q1 a q1)
             (q1 a q2)
             (q1 b q2)
             (q2 a q0))
             'q0
             '(q0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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




(defun product-dfa(dfa-0 dfa-1)
  (let ((Q-0 (finite-automaton-states dfa-0))
        (Sigma-0 (finite-automaton-alphabet dfa-0))
        (E-0 (finite-automaton-edges dfa-0))
        (q0-0 (finite-automaton-start dfa-0))
        (F-0 (finite-automaton-accept dfa-0))
        
        (Q-1 (finite-automaton-states dfa-1))
        (Sigma-1 (finite-automaton-alphabet dfa-1))
        (E-1 (finite-automaton-edges dfa-1))
        (q0-1 (finite-automaton-start dfa-1))
        (F-1 (finite-automaton-accept dfa-1))
        
        (QPrime nil)
        (SigmaPrime nil)
        (EPrime nil)
        (q0Prime nil)
        (FPrime nil)
        
        (product nil)
        (result nil)
        (matching0 nil)
        (matching1 nil)
        (newedge nil))

        ;; set SigmaPrime

        ;; set QPrime to cartesian product of Q-0 x Q-1
        (loop for state-0 in Q-0
              do (loop for state-1 in Q-1
                    do (setq product nil)
                       (push state-0 product)
                       (push state-1 product)
                       (push product QPrime)))

        ;; set q0Prime to the state with the union of the start states from QPrime
        (push q0-0 q0Prime)
        (push q0-1 q0Prime)

        ;; set F prime to the states that are in Qprime and both F-0 and F-1
        (loop for state in QPrime
              do (let ((accept1 (car state))
                       (accept2 (cadr state)))
                   (if (and (member accept1 F-1)
                            (member accept2 F-0))
                       (push state FPrime))))

        ;;; set EPrime to the the cartesian product edge
        (loop for (q0 edge0 q1) in E-0
              do (loop for (q2 edge1 q3) in E-1
                      do (if (equal (list edge0) (list edge1))
                             (progn
                               (setq matching0 nil)
                               (setq matching1 nil)
                               (push q0 matching0)
                               (push q2 matching0)
                               (push q1 matching1)
                               (push q3 matching1)
                               (if (and (set-member QPrime matching0)
                                        (set-member QPrime matching1))
                                   (progn
                                       (setq newedge nil)
                                       (push matching1 newedge)
                                       (push edge1 newedge)
                                       (push matching0 newedge)
                                       (push newedge EPrime)))))))

        ;; Visit function (currently unused)
        ;; Transition Function P((l,m),sigma) = (L(l,sigma),M(m,sigma))
        (labels ((visit (q1 q2 QPrime Eprime)
                   (let ((q1Prime nil)
                         (q2Prime nil)
                         (q-Prime nil)
                         (result nil))
                     (loop for sigma in SigmaPrime
                           do (push (union q1 sigma) q1Prime)
                               (push (union q2 sigma) q2Prime)
                               (push (union q1Prime q2Prime) q-Prime)
                               (if (and (not (equal q1Prime nil)) 
                                        (not (equal q2Prime nil)) 
                                        (not (member q-Prime QPrime)))
                                   (progn
                                     (push q-Prime QPrime)
                                     (push (union EPrime (union (q1 q2)) sigma q-Prime) EPrime)
                                     (result visit (q1Prime q2Prime QPrime EPrime)))))
                     (setq QPrime (car result))
                     (setq EPrime (cdr result))
                     QPrime EPrime))))

      ;; make/return product dfa
      ;; have differnt cases for intersection/equivalence/subset?
      (make-fa EPrime q0Prime FPrime)))


;; Compute the intersection between the arguments
(defun dfa-intersection (dfa-0 dfa-1)
  (product-dfa dfa-0 dfa-1))


;;;;;;;;;;;;;;; Test DFA's ;;;;;;;;;;;;;;;;;;;;;
(defun sample-dfa-0 ()
  (make-fa '((a 0 a)
             (a 1 b)
             (b 1 a)
             (b 0 a))
           'a
           '(b)))

(defun sample-dfa-1 ()
  (make-fa '((c 1 c)
             (c 0 d)
             (d 0 d)
             (d 1 c))
           'c
           '(c)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defun dfa-minimize(dfa)
  (let ((dfa_1) (dfa_2) (dfa_3) (dfa_4) (dfa_5) (temp) (accept) (edges) (start) (m_1) (n_1) (o_1) (new))
    (setf new (newstate))
    (setq dfa_1 (dfa-reverse dfa new))
    (setq dfa_2 (nfa->dfa dfa_1))
    (setf new (newstate))
    (setq dfa_3 (dfa-reverse dfa_2 (list new)))  
    (setq dfa_4 (nfa->dfa dfa_3))                   
    (loop for i in (finite-automaton-edges dfa_4) do
     (setq m_1 (reduce #'append (first i)))
     (setq n_1 (second i))
     (setq o_1 (reduce #'append (third i)))
     (push (list m_1 n_1 o_1) edges))
    (setq start (reduce #'append (finite-automaton-start dfa_4)))
    (setq accept (reduce #'append (finite-automaton-accept dfa_4)))
    (make-fa edges start accept)
    ))


(defun dfa-reverse(dfa temp)
  (let ((states) (start) (edges) (epsilon) (accept) (temp_1) (temp_2))
    (setq temp_1 (finite-automaton-accept dfa))
    (setq accept (finite-automaton-start dfa))
    (setq start temp)
    (setq states (finite-automaton-states dfa))
    (push (list start) states)
    (setq epsilon (finite-automaton-alphabet dfa))
    (loop for i in (finite-automaton-edges dfa) do
    (push (reverse i) edges)

    (loop for j in temp_1 do
     (push (list start :epsilon j) edges)))
  (make-fa edges start (list accept))))





;;;;;;;;;; PDF NFAs ;;;;;;;;;;;;;;;;
(defun default-map()
  (make-fa '( 
             (h02-w00 human_up h01-w00)
             (h01-w00 wumpus_down h01-w01)
             (h01-w01 wumpus_eats lose-state)
             (h01-w01 wumpus_right h01-w10)
             (h01-w10 human_down h02-w10)
             (h02-w10 wumpus_right h02-w20)
             (h02-w20 human_up h01-w20)
             (h01-w20 wumpus_down h01-w21)
             (h01-w21 human_down h02-w21)
             (h02-w21 wumpus_down h02-w22)
             (h02-w22 human_up h01-w22)
             (h01-w22 wumpus_up h01-w21)
             (h01-w21 wumpus_left h01-w12)
             (h01-w12 human_down h02-w12)
             (h02-w12 wumpus_right h02-w22)
             (h02-w22 wumpus_left h02-w02)
             (h02-w02 wumpus_eats lose-state)
             (h02-w12 human_up h00-w12)
             (h00-w12 wumpus_right h00-w22)
             (h00-w22 human_down h01-w22)
             (h01-w22 human_right h10-w22)
             (h10-w22 wumpus_up h10-w21)
             (h10-w21 human_right h20-w21)
             (h20-w21 human_escapes win-state)
             (h20-w21 human_left h00-w21)
             (h00-w21 wumpus_down h00-w22)
             (h00-w22 wumpus_up h00-w20)
             (h00-w20 human_down h01-w20)
             (h01-w20 human_right h10-w20)
             (h10-w20 wumpus_down h10-w21)
             (h10-w21 wumpus_left h10-w10)
             (h10-w10 wumpus_eats lose-state)
             (h10-w21 wumpus_left h10-w12)
             (h10-w12 human_right h20-w12)
             (h20-w12 human_escapes win-state)
             (h20-w12 human_left h00-w12)
             (h00-w22 wumpus_left h00-w02)
             (h00-w02 human_down h01-w02)
             (h01-w02 wumpus_up h01-w01)
             (h01-w01 wumpus_right h01-w12)
             (h01-w02 human_right h10-w02)
             (h10-w02 wumpus_up h10-w01)
             (h10-w01 human_right h20-w01)
             (h20-w01 human_escapes win-state)
             (h20-w01 human_left h00-w01)
             (h00-w01 wumpus_down h00-w02)
             (h00-w02 wumpus_up h00-w00)
             (h00-w00 wumpus_eats lose-state)
             (h10-w01 wumpus_right h10-w12)
             (h01-w22 human_right h12-w22)
             (h12-w22 wumpus_up h12-w21)
             (h12-w21 human_right h22-w21)
             (h22-w21 wumpus_down h22-w22)
             (h22-w22 wumpus_eats lose-state)
             (h22-w22 wumpus_up h22-w20)
             (h22-w20 human_up h21-w20)
             (h21-w20 wumpus_down h21-w21)
             (h21-w21 wumpus_eats lose-state)
             (h21-w21 wumpus_left h21-w10)
             (h21-w10 human_down h22-w10)
             (h22-w10 wumpus_right h22-w20)
             (h22-w20 wumpus_left h22-w00)
             (h22-w00 human_up h21-w00)
             (h21-w00 wumpus_down h21-w01)
             (h21-w01 human_down h22-w01)
             (h22-w01 wumpus_down h22-w02)
             (h22-w02 human_up h21-w02)
             (h21-w02 wumpus_up h21-w01)
             (h21-w01 wumpus_right h21-w12)
             (h21-w12 human_down h22-w12)
             (h22-w12 wumpus_right h22-w22)
             (h22-w22 wumpus_left h22-w02)
             (h22-w12 human_up h20-w12)
             (h21-w02 human_left h12-w02)
             (h12-w02 wumpus_up h12-w01)
             (h12-w01 human_right h22-w01)
             (h22-w01 human_left h02-w01)
             (h02-w01 wumpus_down h02-w02)
             (h02-w02 wumpus_up h02-w00)
             (h12-w01 wumpus_right h12-w12)
             (h12-w12 wumpus_eats lose-state)
             (h22-w02 wumpus_up h22-w00)
             (h22-w01 human_up h20-w01)
             (h21-w01 wumpus_right h21-w10)
             (h21-w00 human_left h12-w00)
             (h12-w00 wumpus_down h12-w01)
             (h12-w01 wumpus_right h12-w10)
             (h12-w10 human_right h22-w10)
             (h22-w10 human_left h02-w10)
             (h22-w10 human_up h20-w10)
             (h20-w10 human_escapes win-state)
             (h21-w20 human_left h12-w20)
             (h12-w20 wumpus_down h12-w21)
             (h12-w21 wumpus_left h12-w10)
             (h22-w21 human_left h02-w21)
             (h12-w21 wumpus_left h12-w12)
             (h02-w22 wumpus_up h02-w20)
             (h02-w21 human_up h00-w21)
             (h01-w21 wumpus_left h01-w10)
             (h01-w20 human_right h12-w20)
             (h02-w20 wumpus_left h02-w00)
             (h02-w10 human_up h00-w10)
             (h00-w10 wumpus_right h00-w20)
             (h00-w20 wumpus_left h00-w00)
             (h01-w00 human_right h12-w00)
             )
           'h02-w00
           '(lose-state win-state))
)

(defun human-escapes-map()
  (make-fa '( 
             (h02-w03 human_down h03-w03)
             (h03-w03 wumpus_eats lose-state)
             (h03-w03 human_up h01-w03)
             (h01-w03 wumpus_up h01-w02)
             (h01-w02 human_down h02-w02)
             (h02-w02 wumpus_eats lose-state)
             (h02-w02 human_up h00-w02)
             (h00-w02 human_escapes win-state)
             )
           'h02-w03
           '(lose-state win-state))
)

(defun wumpus-eats-map()
  (make-fa '( 
             (h04-w02 human_up h03-w02)
             (h03-w02 wumpus_down h03-w03)
             (h03-w03 wumpus_eats lose-state)
             )
           'h04-w03
           '(lose-state win-state))
)

(defun regex-expression()
  (regex->nfa '(:kleene-closure 
                (:union 
                 human_up 
                 wumpus_down  
                 wumpus_right 
                 human_down 
                 wumpus_up 
                 wumpus_left 
                 human_right 
                 human_escapes 
                 human_left)))
)


;;;;;;;;;;;;;;;;;;;;;;
;;;; EXTRA CREDIT ;;;;
;;;;;;;;;;;;;;;;;;;;;;

;; ;; Return the complement of FA
;; (defun fa-complement (fa ))

;; ;; Test whether two FA are equivalent
;; (defun fa-equivalent (fa-0 fa-1))

;; ;; Test whether FA-0 is subseteq of FA-1
;; (defun fa-subseteq (fa-0 fa-1))
