# Lambda Cube+

## Note to self, check the mappings here (name to cube vertex)
Brief implementations of types systems of varying strength
- Untyped Lambda Calculus(λ)
- Simply Typed Lambda Calculus(λ→)
    * With records
- STLC + type operators (λω)
    * with Recursive types
- STLC + dependent types (λΠ)
- STLC + polymorphism - System F (λ2)
    * Predicative
    * Impredicative
- System F Omega
- Dependent Type Theory ?
- Calculus of Constructions


#### Map the names to these PTS 'dependency' representation.
- λ → (∗, ∗) 
- λ2 (∗, ∗) ([], ∗)
- λP (∗, ∗) (∗,[] )
- λP2 (∗, ∗) ([], ∗) (∗, [])
- λω (∗, ∗) ([],[] )
- λω (∗, ∗) ([], ∗) ([],[] )
- λP ω (∗, ∗) (∗,[] ) ([], [])
- λP ω (∗, ∗) ([], ∗) (∗,[] ) ([], [])

## Others
- Martin Lof Type Theory
- Cubical Type Theory
- Modal Dependent TT
- Observational TT
- Dotty?




https://www.seas.harvard.edu/courses/cs252/2016fa/15.pdf
https://ttic.uchicago.edu/~dreyer/course/papers/barendregt.pdf

## TODO
- Modular datatype representation (DTALC or Tagless Final) ?
- Church vs Curry (Cedille)
- Use monad with more visibility for errors (not Maybe)
- Fix type level substitution
- tests
- modular frontend language (parsec)
