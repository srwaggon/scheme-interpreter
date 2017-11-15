
(define apply-in-underlying-scheme apply)

(define (eval exp env)
  (cond [(self-evaluating? exp) exp]
        [(variable? exp) (lookup-variable-value exp env)]
        [(quoted? exp) (text-of-quotation exp)]
        [(assignment? exp) (eval-assignment exp env)]
        [(definition? exp) (eval-definition exp env)]
        [(if? exp) (eval-if exp env)]
        [(lambda? exp) (make-procedure (lambda-parameters exp)
                                       (lambda-body exp)
                                       env)]
        [(begin? exp) (eval-sequence (begin-actions exp) env)]
        [(cond? exp) (eval (cond->if exp) env)]
        [(application? exp) (let* ([oper (eval (operator exp) env)]
                                   [values (list-of-values (operands exp) env)])
                              (apply-custom oper values))]
        [else (error 'eval "Unknown expression type -- EVAL ~s" exp)]))

(define (apply-custom procedure arguments)
  (cond [(primitive-procedure? procedure) (apply-primitive-procedure procedure arguments)]
        [(compound-procedure? procedure)
         (let* ([body (procedure-body procedure)]
                [parameters (procedure-parameters procedure)]
                [proc-environment (procedure-environment procedure)]
                [environment (extend-environment parameters arguments proc-environment)])
           (eval-sequence body environment))]
        [else (error 'apply-custom "Unknown procedure type -- APPLY ~s" procedure)]))

(define (list-of-values exps env)
  (if (no-operands? exps)
      '()
      (cons (eval (first-operand exps) env)
            (list-of-values (rest-operands exps) env))))

(define (eval-if exp env)
  (if (true? (eval (if-predicate exp) env))
      (eval (if-consequent exp) env)
      (eval (if-alternative exp) env)))

(define (true? x)
  (not (eq? x #f)))

(define (false? x)
  (eq? x #f))

(define (eval-sequence exps env)
  (cond [(last-exp? exps) (eval (first-exp exps) env)]
        [else (eval (first-exp exps) env)
              (eval-sequence (rest-exps exps) env)]))

(define (eval-assignment exp env)
  (set-variable-value! (assignment-variable exp)
                       (eval (assignment-value exp) env)
                       env)
  'ok)

(define (eval-definition exp env)
  (define-variable!
    (definition-variable exp)
    (eval (definition-value exp) env)
    env)
  'ok)

(define (self-evaluating? exp)
  (cond [(number? exp) #t]
        [(string? exp) #t]
        [else #f]))

(define (variable? exp) (symbol? exp))

(define (quoted? exp)
  (tagged-list? exp 'quote))

(define (text-of-quotation exp) (cadr exp))

(define (tagged-list? exp tag)
  (if (pair? exp)
      (eq? (car exp) tag)
      #f))

(define (assignment? exp)
  (tagged-list? exp 'set!))
(define (assignment-variable exp) (cadr exp))
(define (assignment-value exp) (caddr exp))

(define (definition? exp)
  (tagged-list? exp 'define))
(define (definition-variable exp)
  (if (symbol? (cadr exp))
      (cadr exp)
      (caadr exp)))
(define (definition-value exp)
  (if (symbol? (cadr exp))
      (caddr exp)
      (make-lambda (cdadr exp)
                   (cddr exp))))

(define (lambda? exp) (tagged-list? exp 'lambda))
(define (lambda-parameters exp) (cadr exp))
(define (lambda-body exp) (cddr exp))

(define (make-lambda parameters body)
  (cons 'lambda (cons parameters body)))

(define (if? exp) (tagged-list? exp 'if))
(define (if-predicate exp) (cadr exp))
(define (if-consequent exp) (caddr exp))
(define (if-alternative exp)
  (if (not (null? (cdddr exp)))
      (cadddr exp)
      'false))

(define (make-if predicate consequent alternative)
  (list 'if predicate consequent alternative))

(define (begin? exp) (tagged-list? exp 'begin))
(define (begin-actions exp) (cdr exp))
(define (last-exp? seq) (null? (cdr seq)))
(define (first-exp seq) (car seq))
(define (rest-exps seq) (cdr seq))

(define (sequence-exp seq)
  (cond [(null? seq) seq]
        [(last-exp? seq) (first-exp seq)]
        [else (make-begin seq)]))

(define (make-begin seq) (cons 'begin seq))

(define (application? exp) (pair? exp))
(define (operator exp) (car exp))
(define (operands exp) (cdr exp))
(define (no-operands? ops) (null? ops))
(define (first-operand ops) (car ops))
(define (rest-operands ops) (cdr ops))

(define (cond? exp) (tagged-list? exp 'cond))
(define (cond-clauses exp) (cdr exp))
(define (cond-else-caluse? clause) (eq? (cond-predicate clause) 'else))
(define (cond-predicate clause) (car clause))
(define (cond-action clause) (cdr clause))
(define (cond->if exp) (expand-clauses (cond-clauses exp)))

(define (expand-clauses clauses)
  (if (null? clauses)
      'false
      (let ((first (car clauses))
            (rest (cdr clauses)))
        (if (cond-else-clause? first)
            (if (null? rest)
                (sequence->exp (cond-actions first))
                (error 'expand-clauses "ELSE clause isn't last -- COND->IF ~s" clauses))
            (make-if (cond-predicate first)
                     (sequence-exp (cond-actions first))
                     (expand-clauses rest))))))


(define (let? exp) (tagged-list? exp 'let))


(define (make-procedure parameters body env)
  (list 'procedure parameters body env))
(define (compound-procedure? p)
  (tagged-list? p 'procedure))
(define (procedure-parameters p) (cadr p))
(define (procedure-body p) (caddr p))
(define (procedure-environment p) (cadddr p))

(define (enclosing-environment env) (cdr env))
(define (get-first-frame env) (car env))
(define the-empty-environment '())

(define (make-frame variables values)
  (list variables values))
(define (get-frame-variables frame) (car frame))
(define (get-frame-values frame) (cadr frame))
(define (add-binding-to-frame! var val frame)
  (set-car! frame (cons var (car frame)))
  (set-cdr! frame (list (cons val (cadr frame)))))

(define (extend-environment vars vals base-env)
  (if (= (length vars) (length vals))
      (cons (make-frame vars vals) base-env)
      (if (< (length vars) (length vals))
          (error 'extend-environment "Too many arguments supplied ~s" vars vals)
          (error 'extend-environment "Too few arguments supplied ~s" vars vals))))

(define (lookup-variable-value var env)
  (define (env-loop env)
    (define (scan-frame vars vals)
      (cond [(null? vars) (env-loop (enclosing-environment env))]
            [(eq? var (car vars)) (car vals)]
            [else (scan-frame (cdr vars) (cdr vals))]))
    (if (eq? env the-empty-environment)
        (error 'lookup-variable-value "Unbound variable ~s" var)
        (let* ([frame (get-first-frame env)]
               [variables (get-frame-variables frame)]
               [values (get-frame-values frame)])
          (scan-frame variables values))))
  (env-loop env))

(define (set-variable-value! var val env)
  (define (env-loop env)
    (define (scan-frame vars vals)
      (cond [(null? vars) (env-loop (enclosing-environment env))]
            [(eq? var (car vars)) (set-car! vals val)]
            [else (scan-frame (cdr vars) (cdr vals))]))
    (if (eq? env the-empty-environment)
        (error 'set-variable-value! "Unbound variable -- SET! ~s" var)
        (let* ([frame (get-first-frame env)]
               [variables (get-frame-variables frame)]
               [values (get-frame-values frame)])
          (scan-frame variables values))))
  (env-loop env))

(define (define-variable! var val env)
  (let* ([frame (get-first-frame env)]
         [variables (get-frame-variables frame)]
         [values (get-frame-values frame)])
    (define (scan-frame vars vals)
      (cond [(null? vars) (add-binding-to-frame! var val frame)]
            [(eq? var (car vars)) (set-car! vals val)]
            [else (scan-frame (cdr vars) (cdr vals))]))
    (scan-frame variables values)))

(define (primitive-procedure? proc)
  (tagged-list? proc 'primitive))

(define (primitive-implementation proc) (cadr proc))

(define primitive-procedures
  (list (list 'car car)
        (list 'cdr cdr)
        (list 'cons cons)
        (list 'null? null?)
        (list 'list list)
        (list '+ +)
        (list '- -)
        (list '* *)
        (list '/ /)
        (list 'mod mod)
        (list '= =)
        (list '< <)
        (list '> >)
        (list '>= >=)
        (list '<= <=)
        (list 'zero? zero?)
        (list 'eq? eq?)
        ))

(define (primitive-procedure-names)
  (map car primitive-procedures))

(define (primitive-procedure-objects)
  (map (lambda (proc) (list 'primitive (cadr proc)))
       primitive-procedures))

(define (apply-primitive-procedure proc args)
  (primitive-implementation proc)
  (apply-in-underlying-scheme (primitive-implementation proc) args))

(define (setup-environment)
  (let* ([names (primitive-procedure-names)]
         [objects (primitive-procedure-objects)]
         [initial-env (extend-environment names objects the-empty-environment)])
    (define-variable! 'true #t initial-env)
    (define-variable! 'false #f initial-env)
    initial-env))

(define the-global-environment (setup-environment))

(define input-prompt ">> ")

(define (driver-loop)
  (prompt-for-input input-prompt)
  (let* ([output (eval (read) the-global-environment)])
    (user-print output))
  (driver-loop))

(define (prompt-for-input string)
  (newline) (newline) (display string))

(define (user-print object)
  (if (compound-procedure? object)
      (display (list 'compound-procedure
                     (procedure-parameters object)
                     (procedure-body object)
                     '<procedure-env>))
      (display object)))

(define the-global-environment (setup-environment))
;; (driver-loop)
