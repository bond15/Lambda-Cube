# Lambda Cube+

## Note to self, check the mappings here (name to cube vertex)
Brief implementations of types systems of varying strength
- Untyped Lambda Calculus(λ) :white_check_mark:
- Simply Typed Lambda Calculus(λ→) :white_check_mark:
    * With records :white_check_mark:
- STLC + type operators (λω) :white_check_mark:
    * with (Iso) Recursive types :white_check_mark:
- STLC + dependent types (λΠ) :white_check_mark:
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


## Sources
- https://www.seas.harvard.edu/courses/cs252/2016fa/15.pdf
- https://ttic.uchicago.edu/~dreyer/course/papers/barendregt.pdf
- https://www.andres-loeh.de/LambdaPi/LambdaPi.pdf
   * Intro to Lambda PI (demonstrates engineering niceties like Bidirectional type checking, locall nameless representaiton, higher order abstract syntax)
   
- http://www.cse.chalmers.se/~ulfn/papers/thesis.pdf
   *  Ulf Thesis (Agda)
   
- https://www.semanticscholar.org/reader/6d2eb533669ee63b77d059f2087a48594f498b8a
   * Pi forall


## TODO
- Modular datatype representation (DTALC or Tagless Final) ?
- Church vs Curry (Cedille)
- Use monad with more visibility for errors (not Maybe)
- Fix type level substitution
- tests
- modular frontend language (parsec)
