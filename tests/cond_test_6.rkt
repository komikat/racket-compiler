; (let [(x (+ 2 (if #t 3 1)))] 
;     (let [(y (+ x 4))]
;         (if (or (eq? y x) (> y x))
;             y x)))
(let [(x (+ 2 (if #t 3 1)))] x)