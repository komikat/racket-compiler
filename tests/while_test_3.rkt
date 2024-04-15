(let ([sum 0]) (let ([i 5])
    (begin
        (while (and (> i 0) (> i 1))
            (begin
            (set! sum (+ sum i)) (set! i (- i 1))))
    sum)))