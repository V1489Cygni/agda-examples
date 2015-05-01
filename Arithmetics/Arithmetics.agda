module Arithmetics where

  module Eq where

    data _≡_ {A : Set} : A → A → Set where
      refl : {n : A} → n ≡ n

    infix 4 _≡_

    sym : {A : Set} → {a b : A} → a ≡ b → b ≡ a
    sym refl = refl

    _~_ : {A : Set} → {a b c : A} → a ≡ b → b ≡ c → a ≡ c
    refl ~ refl = refl

    infixl 5 _~_

    _←_ : {A B : Set} → {a b : A} → (f : A → B) → a ≡ b → f a ≡ f b
    f ← refl = refl

    infixr 6 _←_

  open Eq

  module Monoid where

    record Monoid (A : Set)(f : A → A → A)(e : A) : Set where
      field
        assoc : (a b c : A) → f (f a b) c ≡ f a (f b c)
        e₁ : (a : A) → f e a ≡ a
        e₂ : (a : A) → f a e ≡ a

  open Monoid

  module Nat where

    data ℕ : Set where
      zero : ℕ
      succ : ℕ → ℕ

    one : ℕ
    one = succ zero

  open Nat

  module Addition where

    _+_ : ℕ → ℕ → ℕ
    zero + n = n
    (succ n) + m = succ (n + m)

    infixl 7 _+_

    add-e₁ : (n : ℕ) → zero + n ≡ n
    add-e₁ _ = refl

    add-e₂ : (n : ℕ) → n + zero ≡ n
    add-e₂ zero = refl
    add-e₂ (succ n) = succ ← add-e₂ n

    add-assoc : (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
    add-assoc zero _ _ = refl
    add-assoc (succ a) b c = succ ← add-assoc a b c

    add-monoid : Monoid ℕ _+_ zero
    add-monoid = record { assoc = add-assoc ; e₁ = add-e₁ ; e₂ = add-e₂ }

    add-succ-ins₁ : (n m : ℕ) → succ (n + m) ≡ succ n + m
    add-succ-ins₁ zero _ = refl
    add-succ-ins₁ (succ n) m = succ ← add-succ-ins₁ n m

    add-succ-ins₂ : (n m : ℕ) → succ (n + m) ≡ n + succ m
    add-succ-ins₂ zero _ = refl
    add-succ-ins₂ (succ n) m = succ ← add-succ-ins₂ n m

    add-com : (n m : ℕ) → n + m ≡ m + n
    add-com zero m = sym (add-e₂ m)
    add-com (succ n) m = succ ← add-com n m ~ add-succ-ins₂ m n

    add-perm : (a b c : ℕ) → a + (b + c) ≡ b + (a + c)
    add-perm a b c = sym (add-assoc a b c) ~ (λ x → x + c) ← add-com a b ~ add-assoc b a c

  open Addition

  module Multiplication where

    _*_ : ℕ → ℕ → ℕ
    zero * n = zero
    (succ n) * m = m + n * m

    infixl 8 _*_

    mul-z₁ : (n : ℕ) → zero * n ≡ zero
    mul-z₁ _ = refl

    mul-z₂ : (n : ℕ) → n * zero ≡ zero
    mul-z₂ zero = refl
    mul-z₂ (succ n) = (_+_ zero) ← mul-z₂ n

    mul-e₁ : (n : ℕ) → one * n ≡ n
    mul-e₁ n = refl ~ (_+_ n) ← mul-z₁ n ~ add-e₂ n

    mul-e₂ : (n : ℕ) → n * one ≡ n
    mul-e₂ zero = refl
    mul-e₂ (succ n) = succ ← mul-e₂ n

    mul-dist : (a b c : ℕ) → (a + b) * c ≡ a * c + b * c
    mul-dist zero _ _ = refl
    mul-dist (succ a) b c = (_+_ c) ← mul-dist a b c ~ sym (add-assoc c (a * c) (b * c))

    mul-assoc : (a b c : ℕ) → (a * b) * c ≡ a * (b * c)
    mul-assoc zero _ _ = refl
    mul-assoc (succ a) b c = mul-dist b (a * b) c ~ (_+_ (b * c)) ← mul-assoc a b c

    mul-monoid : Monoid ℕ _*_ one
    mul-monoid = record { assoc = mul-assoc ; e₁ = mul-e₁ ; e₂ = mul-e₂ }

    mul-add-ins₁ : (n m : ℕ) → m + (n * m) ≡ succ n * m
    mul-add-ins₁ zero _ = refl
    mul-add-ins₁ (succ n) m = (_+_ m) ← mul-add-ins₁ n m

    mul-add-ins₂ : (n m : ℕ) → n + n * m ≡ n * succ m
    mul-add-ins₂ zero _ = refl
    mul-add-ins₂ (succ n) m = ((_+_ (succ n)) ← sym (mul-add-ins₁ n m) ~ succ ← add-perm n m (n * m)) ~ (_+_ (succ m)) ← mul-add-ins₂ n m

    mul-com : (n m : ℕ) → n * m ≡ m * n
    mul-com zero m = sym (mul-z₂ m)
    mul-com (succ n) m = (_+_ m) ← mul-com n m ~ mul-add-ins₂ m n

  open Multiplication
