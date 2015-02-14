module SimpleSort where

open import Data.Nat hiding (compare)
open import Data.List
open import Relation.Binary.Core

data _∨_ (A B : Set) : Set where
  fst : A → A ∨ B
  snd : B → A ∨ B

compare : ∀ n m → (n ≤ m) ∨ (m ≤ n)
compare zero _ = fst z≤n
compare _ zero = snd z≤n
compare (suc n) (suc m) with compare n m
compare (suc n) (suc m) | fst n≤m = fst (s≤s n≤m)
compare (suc n) (suc m) | snd m≤n = snd (s≤s m≤n)

next-eq : {l₁ l₂ : List ℕ} → {n : ℕ} → l₁ ≡ l₂ → (n ∷ l₁) ≡ (n ∷ l₂)
next-eq refl = refl

module Sorted where

  data _↓_ : ℕ → List ℕ → Set where
    n↓[] : {n : ℕ} → n ↓ []
    n↓xl : (n x : ℕ) → (l : List ℕ) → n ≤ x → n ↓ (x ∷ l)

  data _↑_ : ℕ → List ℕ → Set where
    n↑[] : {n : ℕ} → n ↑ []
    n↑xl : {n : ℕ} → {l : List ℕ} → (x : ℕ) → n ↑ l → x ≤ n → n ↑ (x ∷ l)

  data Sorted : List ℕ → Set where
    empty : Sorted []
    ins-s : {l₁ l₂ : List ℕ} → (n : ℕ) → Sorted (l₁ ++ l₂) → n ↑ l₁ → n ↓ l₂ → Sorted (l₁ ++ (n ∷ l₂))

module Permutation where

  data _≈_ : List ℕ → List ℕ → Set where
    l≈l   : {l₁ l₂ : List ℕ} → l₁ ≡ l₂ → l₁ ≈ l₂
    ins-p : {l : List ℕ} → (n : ℕ) → (l₁ l₂ : List ℕ) → l ≈ (l₁ ++ l₂) → (n ∷ l) ≈ (l₁ ++ (n ∷ l₂))
    trans : {l₁ l₂ l₃ : List ℕ} → l₁ ≈ l₂ → l₂ ≈ l₃ → l₁ ≈ l₃

open Sorted
open Permutation

record Partition (n : ℕ)(l : List ℕ) : Set where
  constructor ⟨_,_,_,_,_⟩
  field
    l₁   : List ℕ
    l₂   : List ℕ
    eq   : l ≡ (l₁ ++ l₂)
    n↑l₁ : n ↑ l₁
    n↓l₂ : n ↓ l₂

record SortedList (l : List ℕ) : Set where
  constructor ⟨_,_,_⟩
  field
    sl   : List ℕ
    l≈sl : l ≈ sl
    srt  : Sorted sl

nextPartition : {n : ℕ} → {l : List ℕ} → (x : ℕ) → x ≤ n → Partition n l → Partition n (x ∷ l)
nextPartition x x≤n p = ⟨ x ∷ (Partition.l₁ p) , Partition.l₂ p , next-eq (Partition.eq p) , n↑xl x (Partition.n↑l₁ p) x≤n , Partition.n↓l₂ p ⟩

find : (n : ℕ) → (l : List ℕ) → Partition n l
find n [] = ⟨ [] , [] , refl , n↑[] , n↓[] ⟩
find n (x ∷ xs) with compare n x
find n (x ∷ xs) | fst n≤x = ⟨ [] , (x ∷ xs) , refl , n↑[] , (n↓xl n x xs n≤x) ⟩
find n (x ∷ xs) | snd x≤n = nextPartition x x≤n p where p = find n xs

lemma : {l : List ℕ} → (l₁ l₂ : List ℕ) → l ≡ (l₁ ++ l₂) → Sorted l → Sorted (l₁ ++ l₂)
lemma _ _ refl s = s

insert : {l : List ℕ} → (n : ℕ) → SortedList l → SortedList (n ∷ l)
insert n s = let p = find n (SortedList.sl s)
             in let l₁ = Partition.l₁ p
                    l₂ = Partition.l₂ p
                    pm = SortedList.l≈sl s
                    eq = Partition.eq p
                    n↑l₁ = Partition.n↑l₁ p
                    n↓l₂ = Partition.n↓l₂ p
                in ⟨ l₁ ++ (n ∷ l₂) , ins-p n l₁ l₂ (trans pm (l≈l eq)) , ins-s n (lemma l₁ l₂ eq (SortedList.srt s)) n↑l₁ n↓l₂ ⟩

sort : (l : List ℕ) → SortedList l
sort [] = ⟨ [] , l≈l refl , empty ⟩
sort (x ∷ xs) = insert x (sort xs)
