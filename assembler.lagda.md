```agda
module Assembler where
```

## Imports
```agda
  open import Data.Nat using (ℕ; z≤n; s≤s; _<_; _<?_; zero; suc)
  open import Data.Fin using (Fin; fromℕ≤; fromℕ; raise; _-_; reduce≥; 0F; 1F; 2F; 3F; 4F; 5F; 6F; 7F; 8F; 9F)
  open import Relation.Nullary using (Dec; yes; no)
  open import Data.Maybe using (Maybe; just; nothing)
  open import Function using (_∘_)
  open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
  open import Data.Vec using (Vec; zipWith; _∷_; []; _++_)
  open import Relation.Binary.PropositionalEquality using (_≡_)
  open import Data.Bool using (Bool; true; false; _∨_)
  open import Data.List using (List; _∷_; []; replicate)
  open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)

  open import Common using (8KB; Byte; Nibble; Address)
```

## Hex Literals
```agda
  pattern A = suc 9
  pattern B = suc A
  pattern C = suc B
  pattern D = suc C
  pattern E = suc D
  pattern F = suc E
```

## Fin Literals

Extends definitions from Data.Fin.Base
```agda
  pattern 10F = Fin.suc 9F
  pattern 11F = Fin.suc 10F
  pattern 12F = Fin.suc 11F
  pattern 13F = Fin.suc 12F
  pattern 14F = Fin.suc 13F
  pattern 15F = Fin.suc 14F

  pattern #0 = 0F
  pattern #1 = 1F
  pattern #2 = 2F
  pattern #3 = 3F
  pattern #4 = 4F
  pattern #5 = 5F
  pattern #6 = 6F
  pattern #7 = 7F
  pattern #8 = 8F
  pattern #9 = 9F
  pattern #A = 10F
  pattern #B = 11F
  pattern #C = 12F
  pattern #D = 13F
  pattern #E = 14F
  pattern #F = 15F

```

## OpCode construction
```agda
  data BusWrite : Set where

    ALU   :               BusWrite -- ALU outputs the result of calculation to the bus
    INPUT :               BusWrite -- Hard-wired input buffer outputs to bus
    LIT   : Fin (suc F) → BusWrite -- Literal value from range [0..F] is output to the bus


  data BusRead : Set where

    REG_A    : BusRead -- Register A reads from the bus
    REG_B    : BusRead -- Register B reads from the bus
    RAM_DATA : BusRead -- Value on bus is read into RAM has data to be stored
    RAM_INST : BusRead -- Value on bus is read into RAM as an instructions e.g. addressing

  infixr 5 _⇒_

  data OpCode : Set where

    _⇒_ : BusWrite
        → BusRead
          --------
        → OpCode

  exampleOpCode : OpCode
  exampleOpCode = LIT #3 ⇒ REG_A  
```

## Instructions

An instruction contains its address, the opcode to be stored at that address, and a pointer to the next address. This is implemented in hardware as a pair of EEPROMs, one storing the opcodes to be executed and another storing the next value to be placed into the program counter. Therefore, JUMP instructions are not necessary and sequential instructions need not be placed sequentially in ROM, potentially facilitating some optimisations.

```agda

  IsAddress : ℕ → Set
  IsAddress n = n < 8KB

  infixr 6 _⦂_,_

  data Instruction : Set where

    _⦂_,_ : ∀ {m} {n} → Dec (IsAddress m × Address) → OpCode → Dec (IsAddress n × Address) → Instruction

  raiseTo : ∀ (m : ℕ) → (n : ℕ) → Dec (m < n × Fin n)
  raiseTo m n with m <? n
  raiseTo m n | yes m<n = yes ⟨ m<n , fromℕ≤ m<n ⟩
  raiseTo m n | no ¬m<n = no λ{ ⟨ m<n , _ ⟩ → ¬m<n m<n}

  infixr 7 ⊢_

  ⊢_ : ∀ (n : ℕ) → Dec (IsAddress n × Address)
  ⊢_ n = raiseTo n 8KB

  exampleInstruction : Instruction
  exampleInstruction = ⊢ 3 ⦂ LIT #3 ⇒ REG_A , ⊢ 4

```

## To Binary
```agda

  pattern O = false
  pattern I = true

  _,_,_,_,_,_,_,_b : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool → Byte
  a , b , c , d , e , f , g , h b = a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ []

  _,_,_,_b : Bool → Bool → Bool → Bool → Nibble
  a , b , c , d b = a ∷ b ∷ c ∷ d ∷ []

  encodeNibble : Fin (suc F) → Nibble
  encodeNibble #0 = O , O , O , O b
  encodeNibble #1 = O , O , O , I b
  encodeNibble #2 = O , O , I , O b
  encodeNibble #3 = O , O , I , I b
  encodeNibble #4 = O , I , O , O b
  encodeNibble #5 = O , I , O , I b
  encodeNibble #6 = O , I , I , O b
  encodeNibble #7 = O , I , I , I b
  encodeNibble #8 = I , O , O , O b
  encodeNibble #9 = I , O , O , I b
  encodeNibble #A = I , O , I , O b
  encodeNibble #B = I , O , I , I b
  encodeNibble #C = I , I , O , O b
  encodeNibble #D = I , I , O , I b
  encodeNibble #E = I , I , I , O b
  encodeNibble #F = I , I , I , I b

  assembleBusRead : BusRead → Byte
  assembleBusRead REG_A    = O , O , O , O , O , O , O , O b
  assembleBusRead REG_B    = O , O , O , O , O , O , I , O b
  assembleBusRead RAM_DATA = O , O , O , O , O , O , O , I b
  assembleBusRead RAM_INST = O , O , O , O , O , O , I , I b

  assembleBusWrite : BusWrite → Byte
  assembleBusWrite (LIT x) = encodeNibble x ++ I , O , O , O b
  assembleBusWrite ALU     =   O , O , I , O , O , O , O , O b
  assembleBusWrite INPUT   =   O , O , O , I , O , O , O , O b

  assembleOpCode : OpCode → Byte
  assembleOpCode (busWrite ⇒ busRead) = zipWith _∨_ (assembleBusWrite busWrite) (assembleBusRead busRead)

```

```agda

  program : ℕ → List Instruction → Maybe (List Byte × List (Fin 8KB))
  program padding [] = just ⟨ replicate padding (O , O , O , O , O , O , O , O b) , replicate padding 0F ⟩
  program zero x = just ⟨ [] , [] ⟩
  program (suc padding) (_ ⦂ _ , no _ ∷ _) = nothing
  program (suc padding) (_ ⦂ opcode , yes ⟨ _ , next ⟩ ∷ instructions) with program padding instructions
  ... | nothing = nothing
  ... | just ⟨ signals , gotos ⟩ = just ⟨ assembleOpCode opcode ∷ signals , next ∷ gotos ⟩

```
