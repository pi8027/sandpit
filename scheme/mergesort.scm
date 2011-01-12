
(use util.match)

(define (mergesort less? lst)
  (define (mergesort-iter lst)
    (match lst
      (() '())
      ((x) x)
      (l (mergesort-iter (merge-pairs l)))))
  (define (merge-pairs lst)
    (match lst
      ((x1 x2 . xs) (cons (merge x1 x2) (merge-pairs xs)))
      ((x) (list x))
      (() '())))
  (define (merge l1 l2)
    (match (list l1 l2)
      ((_ ()) l1)
      ((() _) l2)
      (((x . xs) (y . ys)) (if (less? x y) (cons x (merge xs l2)) (cons y (merge l1 ys))))))
  (define (wrap x) (list x))
  (mergesort-iter (map wrap lst)))

;(define (compare-car a b) (<= (car a) (car b)))

;(print (mergesort compare-car '((2 0) (0 0) (4 0) (4 1) (2 1) (3 0) (3 1) (1 0) (0 1) (1 1))))

(print (mergesort >= '(7 3 5 9 2 0 5 1 9 2 3 6 7 0 4 7 1)))

