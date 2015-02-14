module SimpleSort where

open import Data.List
open import Relation.Binary.Core

data _∨_ (A B : Set) : Set where
  fst : A → A ∨ B
  snd : B → A ∨ B

next-eq : {A : Set} → {l₁ l₂ : List A} → {n : A} → l₁ ≡ l₂ → (n ∷ l₁) ≡ (n ∷ l₂)
next-eq refl = refl

module Sorted where

  data ⟨_⟩_↓_ {A : Set} (_≤_ : A → A → Set) : A → List A → Set where
    n↓[] : {n : A} → ⟨ _≤_ ⟩ n ↓ []
    n↓xl : (n x : A) → (l : List A) → n ≤ x → ⟨ _≤_ ⟩ n ↓ (x ∷ l)

  data ⟨_⟩_↑_ {A : Set} (_≤_ : A → A → Set) : A → List A → Set where
    n↑[] : {n : A} → ⟨ _≤_ ⟩ n ↑ []
    n↑xl : {n : A} → {l : List A} → (x : A) → ⟨ _≤_ ⟩ n ↑ l → x ≤ n → ⟨ _≤_ ⟩ n ↑ (x ∷ l)

  data Sorted {A : Set} (_≤_ : A → A → Set) : List A → Set where
    empty : Sorted _≤_ []
    ins-s : {l₁ l₂ : List A} → (n : A) → Sorted _≤_ (l₁ ++ l₂) → ⟨ _≤_ ⟩ n ↑ l₁ → ⟨ _≤_ ⟩ n ↓ l₂ → Sorted _≤_ (l₁ ++ (n ∷ l₂))

module Permutation where

  data _≈_ {A : Set} : List A → List A → Set where
    l≈l   : {l₁ l₂ : List A} → l₁ ≡ l₂ → l₁ ≈ l₂
    ins-p : {l : List A} → (n : A) → (l₁ l₂ : List A) → l ≈ (l₁ ++ l₂) → (n ∷ l) ≈ (l₁ ++ (n ∷ l₂))
    trans : {l₁ l₂ l₃ : List A} → l₁ ≈ l₂ → l₂ ≈ l₃ → l₁ ≈ l₃

open Sorted
open Permutation

record Partition {A : Set} (_≤_ : A → A → Set) (n : A) (l : List A) : Set where
  constructor ⟨_,_,_,_,_⟩
  field
    l₁   : List A
    l₂   : List A
    eq   : l ≡ (l₁ ++ l₂)
    n↑l₁ : ⟨ _≤_ ⟩ n ↑ l₁
    n↓l₂ : ⟨ _≤_ ⟩ n ↓ l₂

record SortedList {A : Set} (_≤_ : A → A → Set) (l : List A) : Set where
  constructor ⟨_,_,_⟩
  field
    sl   : List A
    l≈sl : l ≈ sl
    srt  : Sorted _≤_ sl

nextPartition : {A : Set} → {_≤_ : A → A → Set} → {n : A} → {l : List A} → (x : A) → x ≤ n → Partition _≤_ n l → Partition _≤_ n (x ∷ l)
nextPartition x x≤n p = ⟨ x ∷ (Partition.l₁ p) , Partition.l₂ p , next-eq (Partition.eq p) , n↑xl x (Partition.n↑l₁ p) x≤n , Partition.n↓l₂ p ⟩

find : {A : Set} → {_≤_ : A → A → Set} → ((n m : A) → (n ≤ m) ∨ (m ≤ n)) → (n : A) → (l : List A) → Partition _≤_ n l
find compare n [] = ⟨ [] , [] , refl , n↑[] , n↓[] ⟩
find compare n (x ∷ xs) with compare n x
find compare n (x ∷ xs) | fst n≤x = ⟨ [] , (x ∷ xs) , refl , n↑[] , (n↓xl n x xs n≤x) ⟩
find compare n (x ∷ xs) | snd x≤n = nextPartition x x≤n (find compare n xs)

lemma : {A : Set} → {_≤_ : A → A → Set} → {l : List A} → (l₁ l₂ : List A) → l ≡ (l₁ ++ l₂) → Sorted _≤_ l → Sorted _≤_ (l₁ ++ l₂)
lemma _ _ refl s = s

insert : {A : Set} → {_≤_ : A → A → Set} → ((n m : A) → (n ≤ m) ∨ (m ≤ n)) → {l : List A} → (n : A) → SortedList _≤_ l → SortedList _≤_ (n ∷ l)
insert compare n s = let p = find compare n (SortedList.sl s)
                     in let l₁ = Partition.l₁ p
                            l₂ = Partition.l₂ p
                            pm = SortedList.l≈sl s
                            eq = Partition.eq p
                            n↑l₁ = Partition.n↑l₁ p
                            n↓l₂ = Partition.n↓l₂ p
                        in ⟨ l₁ ++ (n ∷ l₂) , ins-p n l₁ l₂ (trans pm (l≈l eq)) , ins-s n (lemma l₁ l₂ eq (SortedList.srt s)) n↑l₁ n↓l₂ ⟩

sort : {A : Set} → {_≤_ : A → A → Set} → ((n m : A) → (n ≤ m) ∨ (m ≤ n)) → (l : List A) → SortedList _≤_ l
sort compare [] = ⟨ [] , l≈l refl , empty ⟩
sort compare (x ∷ xs) = insert compare x (sort compare xs)
