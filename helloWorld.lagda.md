```agda

open import Agda.Builtin.Unit
open import Data.List using (_∷_; [])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import IO.Primitive

open import Assembler
open import Common
open import Ffi

main : IO ⊤
main = compile (program
  ( (⟨ #0 , #0 ⟩ ⦂ LIT #0 ⇒ REG_A    , ⟨ #0 , #1 ⟩)  -- empty step, can remove?
  ∷ (⟨ #0 , #1 ⟩ ⦂ LIT #2 ⇒ RAM_INST , ⟨ #0 , #2 ⟩)  -- enable 4 bit RAM mode
  ∷ (⟨ #0 , #2 ⟩ ⦂ LIT #2 ⇒ RAM_INST , ⟨ #0 , #3 ⟩)  -- again
  ∷ (⟨ #0 , #3 ⟩ ⦂ LIT #2 ⇒ RAM_INST , ⟨ #0 , #4 ⟩)  -- and again
  ∷ (⟨ #0 , #4 ⟩ ⦂ LIT #0 ⇒ RAM_INST , ⟨ #0 , #5 ⟩)  -- UPPER: Enable cursor
  ∷ (⟨ #0 , #5 ⟩ ⦂ LIT #F ⇒ RAM_INST , ⟨ #0 , #6 ⟩)  -- LOWER: Enable cursor
  ∷ (⟨ #0 , #6 ⟩ ⦂ LIT #4 ⇒ RAM_DATA , ⟨ #0 , #7 ⟩)  -- UPPER: "H"
  ∷ (⟨ #0 , #7 ⟩ ⦂ LIT #8 ⇒ RAM_DATA , ⟨ #0 , #8 ⟩)  -- LOWER: "H"
  ∷ (⟨ #0 , #8 ⟩ ⦂ LIT #6 ⇒ RAM_DATA , ⟨ #0 , #9 ⟩)  -- UPPER: "i"
  ∷ (⟨ #0 , #9 ⟩ ⦂ LIT #9 ⇒ RAM_DATA , ⟨ #0 , #A ⟩)  -- LOWER: "i"
  ∷ (⟨ #0 , #A ⟩ ⦂ LIT #8 ⇒ REG_A    , ⟨ #0 , #B ⟩)  --   8
  ∷ (⟨ #0 , #B ⟩ ⦂ LIT #7 ⇒ REG_B    , ⟨ #0 , #6 ⟩   -- + 7
           IfZero⦂ LIT #8 ⇒ REG_B    , ⟨ #0 , #8 ⟩)  -- = F so repeat "Hi"
  ∷ []
  ))
```
