module Test where

open import SimpleSort

open import Function
open import Data.Nat hiding (compare)
open import Data.Nat.Show
open import Data.List hiding (_++_)

open import IO.Primitive using (IO; putStrLn)
open import Data.String renaming (show to showString)
open import Foreign.Haskell using (Unit)

compare : (n m : ℕ) → (n ≤ m) ∨ (m ≤ n)
compare zero _ = fst z≤n
compare _ zero = snd z≤n
compare (suc n) (suc m) with compare n m
compare (suc n) (suc m) | fst n≤m = fst (s≤s n≤m)
compare (suc n) (suc m) | snd m≤n = snd (s≤s m≤n)

list : List ℕ
list = 5 ∷ 6 ∷ 4 ∷ 3 ∷ 7 ∷ 0 ∷ 2 ∷ [ 1 ]

showList : List ℕ → String
showList [] = ""
showList (x ∷ xs) = (show x) ++ " " ++ (showList xs)

main : IO Unit
main = (putStrLn ∘ toCostring) (showList (SortedList.sl (sort compare list))) 
