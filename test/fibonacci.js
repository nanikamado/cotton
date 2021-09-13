{
    let plusOp = a => b => {
        return a + b;
    };
    let minusOp = a => b => {
        return a - b;
    };
    let fib = (a0) => {
        return (a0 == 0)
            ? 0 : (a0 == 1)
                ? 1 : (plusOp(fib(minusOp(a0)(1)))(fib(minusOp(a0)(2))));
    };
    let main = (a0) => {
        return (a0 === '()') ?
            console.log(fib(4))
            : null;
    };
    main('()');
}