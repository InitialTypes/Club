
## A case study in dependently typed programming

In traditional program verification you first write a program and then
prove that it satisfies the desired properties. Correct-by-construction
dependently typed programming, on the other hand, is the technique of
expressing the desired properties in the type of the program itself.
When done right, the extra precision in the type doesn't get in the way,
and in many cases help, when writing the program. In this talk we'll
write a correct-by-construction type checker for the simply typed lambda
calculus, illustrating the power of dependently typed programming.

### Building

Tested with Agda-2.5.4.2 and the `compat-2.5.4` branch of
[agda-prelude](https://github.com/UlfNorell/agda-prelude), as well as the
current
([3161248](https://github.com/agda/agda/tree/3161248c2dcde48c19246b125a7a2ad0785d9d7a) and
 [809e9dd](https://github.com/UlfNorell/agda-prelude/tree/809e9dd5543a2b837e7285d84eef56445dd8c5d0))
master branches of Agda and agda-prelude. Requires agda-prelude to be listed in
the `~/.agda/libraries` files. See [the user
manual](https://agda.readthedocs.io/en/v2.5.4.2/tools/package-system.html) for
more information.

Compile with

```
agda -c Main.agda
```

Try an example:
```
$ ./Main factorial.lam 7
Type: nat
Term: (λ (plus : nat → nat → nat) → (λ (times : nat → nat → nat) → (λ (fac : nat → nat) → fac) (natrec nat 1 (λ (n : nat) → times (suc n)))) (λ (n : nat) → natrec nat 0 (λ (_ : nat) → plus n))) (λ (n : nat) → natrec nat n (λ (_ : nat) → suc)) 7
Val:  5040
```
