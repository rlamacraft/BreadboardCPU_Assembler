```agda

open import Agda.Builtin.Unit
open import IO.Primitive
open import Data.List using (_∷_; [])

open import Ffi
open import Assembler
open import Common
main : IO ⊤
main = compile` (program 8KB
  ( (#0 ⦂ #0) ⦂ LIT #0 ⇒ REG_A    , (#0 ⦂ #1)  -- empty step, can remove?
  ∷ (#0 ⦂ #1) ⦂ LIT #2 ⇒ RAM_INST , (#0 ⦂ #2)  -- enable 4 bit RAM mode
  ∷ (#0 ⦂ #2) ⦂ LIT #2 ⇒ RAM_INST , (#0 ⦂ #3)  -- again
  ∷ (#0 ⦂ #3) ⦂ LIT #2 ⇒ RAM_INST , (#0 ⦂ #4)  -- and again
  ∷ (#0 ⦂ #4) ⦂ LIT #0 ⇒ RAM_INST , (#0 ⦂ #5)  -- UPPER: Enable cursor
  ∷ (#0 ⦂ #5) ⦂ LIT #F ⇒ RAM_INST , (#0 ⦂ #6)  -- LOWER: Enable cursor
  ∷ (#0 ⦂ #6) ⦂ LIT #4 ⇒ RAM_DATA , (#0 ⦂ #7)  -- UPPER: "H"
  ∷ (#0 ⦂ #7) ⦂ LIT #8 ⇒ RAM_DATA , (#0 ⦂ #8)  -- LOWER: "H"
  ∷ (#0 ⦂ #8) ⦂ LIT #6 ⇒ RAM_DATA , (#0 ⦂ #9)  -- UPPER: "i"
  ∷ (#0 ⦂ #9) ⦂ LIT #9 ⇒ RAM_DATA , (#0 ⦂ #6)  -- LOWER: "i"
  ∷ (#0 ⦂ #A) ⦂ LIT #2 ⇒ RAM_DATA , (#0 ⦂ #B)  -- UPPER: " "
  ∷ (#0 ⦂ #B) ⦂ LIT #0 ⇒ RAM_DATA , (#0 ⦂ #C)  -- LOWER: " "
  ∷ (#0 ⦂ #C) ⦂ LIT #4 ⇒ RAM_DATA , (#0 ⦂ #D)  -- UPPER: "K"
  ∷ (#0 ⦂ #D) ⦂ LIT #B ⇒ RAM_DATA , (#0 ⦂ #E)  -- LOWER: "K"
  ∷ (#0 ⦂ #E) ⦂ LIT #6 ⇒ RAM_DATA , (#0 ⦂ #F)  -- UPPER: "a"
  ∷ (#0 ⦂ #F) ⦂ LIT #1 ⇒ RAM_DATA , (#1 ⦂ #0)  -- LOWER: "a"
  ∷ (#1 ⦂ #0) ⦂ LIT #6 ⇒ RAM_DATA , (#1 ⦂ #1)  -- UPPER: "m"
  ∷ (#1 ⦂ #1) ⦂ LIT #D ⇒ RAM_DATA , (#1 ⦂ #2)  -- LOWER: "m"
  ∷ (#1 ⦂ #2) ⦂ LIT #2 ⇒ RAM_DATA , (#1 ⦂ #3)  -- UPPER: "!"
  ∷ (#1 ⦂ #3) ⦂ LIT #1 ⇒ RAM_DATA , (#1 ⦂ #4)  -- LOWER: "!"
  ∷ (#1 ⦂ #4) ⦂ LIT #2 ⇒ RAM_DATA , (#1 ⦂ #5)  -- UPPER: "!"
  ∷ (#1 ⦂ #5) ⦂ LIT #1 ⇒ RAM_DATA , (#1 ⦂ #6)  -- LOWER: "!"
  ∷ []
  ))
```
