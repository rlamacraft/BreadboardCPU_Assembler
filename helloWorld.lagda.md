```agda

open import Agda.Builtin.Unit
open import IO.Primitive
open import Data.List using (_∷_; [])

open import Ffi
open import Assembler
open import Common

main : IO ⊤
main = compile (program 8KB
  ( ⊢ 0  ⦂ LIT #0 ⇒ REG_A    , ⊢ 1   -- empty step, can remove?
  ∷ ⊢ 1  ⦂ LIT #2 ⇒ RAM_INST , ⊢ 2   -- enable 4 bit RAM mode
  ∷ ⊢ 2  ⦂ LIT #2 ⇒ RAM_INST , ⊢ 3   -- again
  ∷ ⊢ 3  ⦂ LIT #2 ⇒ RAM_INST , ⊢ 4   -- and again
  ∷ ⊢ 4  ⦂ LIT #0 ⇒ RAM_INST , ⊢ 5   -- UPPER: Enable cursor
  ∷ ⊢ 5  ⦂ LIT #F ⇒ RAM_INST , ⊢ 6   -- LOWER: Enable cursor
  ∷ ⊢ 6  ⦂ LIT #4 ⇒ RAM_DATA , ⊢ 7   -- UPPER: "H"
  ∷ ⊢ 7  ⦂ LIT #8 ⇒ RAM_DATA , ⊢ 8   -- LOWER: "H"
  ∷ ⊢ 8  ⦂ LIT #6 ⇒ RAM_DATA , ⊢ 9   -- UPPER: "i"
  ∷ ⊢ 9  ⦂ LIT #9 ⇒ RAM_DATA , ⊢ 10  -- LOWER: "i"
  ∷ ⊢ 10 ⦂ LIT #2 ⇒ RAM_DATA , ⊢ 11  -- UPPER: "!"
  ∷ ⊢ 11 ⦂ LIT #1 ⇒ RAM_DATA , ⊢ 12  -- LOWER: "!"
  ∷ []
  ))

```
