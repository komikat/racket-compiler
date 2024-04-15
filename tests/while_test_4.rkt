(let ([x2 10]) 
    (let ([y3 0])
        (+ (+ (begin
                (set! y3 4)
                x2) 
            (begin
                (set! x2 8)
                y3)) 
        x2)))