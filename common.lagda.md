```agda
module Common where

open import Data.Nat using (ℕ; suc; _^_)
open import Data.Vec using (Vec)
open import Data.Bool using (Bool)
open import Data.Fin using (Fin; 0F; 1F; 2F; 3F; 4F; 5F; 6F; 7F; 8F; 9F)
```

## Boolean General Use
```agda

Nibble : Set
Nibble = Vec Bool 4

Byte : Set
Byte = Vec Bool 8

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

## ROM related
```
8KB : ℕ        -- size of the EEPROMs
8KB = 2 ^ 13

data Address : Set where

  _⦂_ : Fin (suc F) → Fin (suc F) → Address


```

