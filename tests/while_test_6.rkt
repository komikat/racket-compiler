(let [(x 5)] 
    (let [(y 10)]
        (begin 
            (begin
                (set! y 12)
                (set! x 40)
                    y)
            x)))