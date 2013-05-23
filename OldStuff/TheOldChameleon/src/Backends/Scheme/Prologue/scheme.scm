;;; begin prologue
;;; strict implementation
;;; error functions
(define hpattern%u004datch%u0046ailed! (lambda (s)
					 (display "patternMatchFailed!: ")
					 (for-each display s)
					 (/ 0)))
(define hno%u0053uch%u0046ield! (lambda (s)
				  (display "noSuchField!: ")
				  (for-each display s)
				  (/ 0)))
(define huninitialised%0046ield! (lambda (s)
				   (display "uninitialisedField!: ")
				   (for-each display s)
				   (/ 0)))
;;; built-in list operations
(define h%u005b%u005d '())
(define ?h%u005b%u005d null?)
(define h: (lambda (x) (lambda (y) (cons x y))))
(define ?h: pair?)
(define h:.0 car)
(define h:.1 cdr)
;;; built-in boolean operations
(define h%u0046alse #f)
(define h%u0054rue #t)
(define ?h%u0046alse not)
(define ?h%u0054rue (lambda (x) x))
;;; built-in unit operations
(define h%u0028%u0029 'nothing)
(define ?h%u0028%u0029 symbol?)
;;; built-in tuple operations
(define h%u0028%u002c%u0029 (lambda (x) (lambda (y) (vector x y))))
(define ?h%u0028%u002c%u0029 vector?)
(define h%u0028%u002c%u002c%u0029  (lambda (x) (lambda (y) (lambda (z) (vector x y z)))))
(define ?h%u0028%u002c%u002c%u0029 vector?)
(define h%u0028%u002c%u002c%u002c%u0029 (lambda (x) (lambda (y) (lambda (z) (lambda (w) (vector x y z w))))))
(define ?h%u0028%u002c%u002c%u002c%u0029 vector?)
(define h%u0028%u002c%u002c%u002c%u002c%u0029 (lambda (x) (lambda (y) (lambda (z) (lambda (w) (lambda (v) (vector x y z w v)))))))
(define ?h%u0028%u002c%u002c%u002c%u002c%u0029 vector?)
(define h%u0028%u002c%u002c%u002c%u002c%u002c%u0029 (lambda (x) (lambda (y) (lambda (z) (lambda (w) (lambda (v) (lambda (u) (vector x y z w v u))))))))
(define ?h%u0028%u002c%u002c%u002c%u002c%u002c%u0029 vector?)
(define h%u0028%u002c%u002c%u002c%u002c%u002c%u002c%u0029 (lambda (x) (lambda (y) (lambda (z) (lambda (w) (lambda (v) (lambda (u) (lambda (t) (vector x y z w v u t)))))))))
(define ?h%u0028%u002c%u002c%u002c%u002c%u002c%u002c%u0029 vector?)
;;; end prologue
