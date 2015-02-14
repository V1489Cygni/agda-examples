module Test where

open import SimpleSort

open import Function
open import Data.Nat
open import Data.Nat.Show
open import Data.List hiding (_++_)

open import IO.Primitive using (IO; putStrLn)
open import Data.String renaming (show to showString)
open import Foreign.Haskell using (Unit)

l : List ℕ
l = 4 ∷ (3 ∷ (7 ∷ (0 ∷ (2 ∷ [ 1 ]))))

showList : List ℕ → String
showList [] = ""
showList (x ∷ xs) = (show x) ++ " " ++ (showList xs)

s : SortedList l
s = sort l

main : IO Unit
main = (putStrLn ∘ toCostring) (showList (SortedList.sl s)) 
