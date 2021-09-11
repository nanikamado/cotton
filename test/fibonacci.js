{
    let fib = (a0) => {
        return (a0 == 0) ?
            0 : (a0 == 1) ?
                1 : (fib(a0 - 1) + fib(a0 - 2));
    };
    let main = (a0) => {
        return (a0 === '()') ?
            console.log(fib(4))
            : null;
    };
    main('()');
}