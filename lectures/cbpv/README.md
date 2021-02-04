Call-by-Push-Value (CBPV)
=========================

Motivation: lazy effects.
```
  foo :: a -> IO a
  foo = do
    putStrLn "function"
    \ a -> do
       putStrLn "argument"
       return a
```

[Introduction to monads and monad algebras](Hutton.hs)

Papers:

* [Graded Call-By-Push-Value](http://www.cse.chalmers.se/~abela/popl21.pdf)
  Rejected from POPL 21

* [Normalization by Evaluation for Call-By-Push-Value and Polarized Lambda Calculus](http://www.cse.chalmers.se/~abela/ppdp19.pdf)
  PPDP 19

Literature:

* Paul-Blain Levy
  [Call-by-push-value: Decomposing call-by-value and call-by-name](https://dl.acm.org/doi/abs/10.1007/s10990-006-0480-6)

* Frank Pfenning,
  [Lecture notes on CBPV](https://www.cs.cmu.edu/~fp/courses/15816-f16/lectures/21-cbpv.pdf)

  These lecture notes give, starting at natural deduction, a
  polarization of formulas that yields the CBPV calculus.  Formulas
  are separated into positive or _value_ types that can serve as
  hypotheses (and also as conclusion) and negative or _computation_
  types that can only serve as conclusion.  The positive formulas are
  disjoint sums (tagged unions) and eager tuples, both with
  sequent-style elimination rules (i.e., pattern matching), plus
  embedding of negative formulas which is interpreted as _thunking_.
  The negative formulas are function types and lazy tuples (record
  types), both with natural-deduction style elimination rules.  Note
  that the domain of a function type is positive, since it serves as
  hypothesis in the typing of the function body.  Further, positive
  types are embedded into negative types, interpreted as the _monad_
  with elimination via _bind_.

  The lecture notes argue how the CBPV calculus arises necessarily
  from the polarization of formulas and the decision that only
  positive formulas can play the role of hypotheses.
