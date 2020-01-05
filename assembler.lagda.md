```agda
module Assembler where
```

## Imports
```agda
  open import Data.Nat using (ℕ; z≤n; s≤s; _<_; _<?_; zero; suc)
  open import Data.Fin using (Fin; fromℕ≤; fromℕ; raise; _-_; reduce≥; 0F; 1F; 2F; 3F; 4F; 5F; 6F; 7F; 8F; 9F; toℕ)
  open import Relation.Nullary using (Dec; yes; no)
  open import Data.Maybe using (Maybe; just; nothing)
  open import Function using (_∘_)
  open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
  open import Data.Vec using (Vec; zipWith; _∷_; []; _++_; fromList; replicate)
  open import Relation.Binary.PropositionalEquality using (_≡_)
  open import Data.Bool using (Bool; true; false; _∨_)
  open import Data.List using (List; _∷_; [])
  open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)

  open import Common -- using (8KB; Byte; Nibble; Address)
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

  infixr 6 _⦂_,_

  data Instruction : Set where
    _⦂_,_ : Address → OpCode → Address → Instruction

  raiseTo : ∀ (m : ℕ) → (n : ℕ) → Dec (m < n × Fin n)
  raiseTo m n with m <? n
  raiseTo m n | yes m<n = yes ⟨ m<n , fromℕ≤ m<n ⟩
  raiseTo m n | no ¬m<n = no λ{ ⟨ m<n , _ ⟩ → ¬m<n m<n}

  exampleInstruction : Instruction
  exampleInstruction = (#0 ⦂ #3) ⦂ LIT #3 ⇒ REG_A , (#0 ⦂ #4)

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

  addressToByte : Address → Byte
  addressToByte (upper ⦂ lower) = encodeNibble upper ++ encodeNibble lower

```

# Program

Returns a pair of vectors of bytes. The first vector is the compiled go-to addresses that will be written to the go-to ROM and the second vector is the compiled op-codes that will be written to the signals ROM.

```agda

  allZeros : Byte
  allZeros = (addressToByte (#0 ⦂ #0))
  
  program : (n : ℕ) → List Instruction → (Vec Byte n) × (Vec Byte n)
  program 0F         _        = ⟨ [] , [] ⟩
  program (suc _)    []       = ⟨ replicate allZeros , replicate allZeros ⟩
  program (suc size) (_ ⦂ opcode , next ∷ xs) with program size xs            -- NOTE: current address is unused i.e. it is a mandatory comment
  ... | ⟨ go-to , signals ⟩ = ⟨ (addressToByte next ∷ go-to) , (assembleOpCode opcode) ∷ signals ⟩
```
