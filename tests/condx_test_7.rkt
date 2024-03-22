(let [(x (+ 2 (if #t 3 1)))] 
    (let [(y (+ x 4))]
        (if (> x 4)
            y x)))