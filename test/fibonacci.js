{
    let $plus = a => b => {
        return a + b;
    };
    let $minus = a => b => {
        return a - b;
    };
    let println = a => {
        console.log(a);
    };
    let fib = (a0) => {
        return (a0 == 0)
            ? 0 : (a0 == 1)
                ? 1 : ($plus(fib($minus(a0)(1)))(fib($minus(a0)(2))));
    };
    let main = (a0) => {
        return (a0 === '()') ?
            println(fib(4))
            : null;
    };
    main('()');
}