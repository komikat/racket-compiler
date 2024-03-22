; (if (and 
;         (and (eq? 1 2) 
;             (or #f (let [(x 1)] (> x 0))))
;         (or 
;             (or 
;                 (and (eq? 1 2) 
;                     (and (> 1 2) #t))
;                 (or (let [(x (+ 9 (- 8)))]
;                         (let [(y 2)] 
;                             (> x y)))
;                     #f))
;             (not (if (> 8 2) (or (not #t) (not #f)) (not #t)))))
;     18 14)

(if  
        (and (eq? 1 2) 
            (or #f (let [(x 1)] (> x 0))))
        
    18 14)