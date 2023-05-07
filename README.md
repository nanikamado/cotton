# Cotton
Cotton is a simple functional programming language.

## Installing

```
cargo install --git 'https://github.com/nanikamado/cotton.git' --features language-server
```

### Dependencies
- cargo
- clang

## Run

```
cotton examples/helloworld.cot --emit-c | clang -x c -o /tmp/a - && /tmp/a
```

or

```
cotton examples/helloworld.cot
```

## Playground

https://gitpod.io/#https://github.com/nanikamado/cotton-playground
