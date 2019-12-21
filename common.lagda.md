```
module Common where

open import Data.Nat using (ℕ; _^_)
open import Data.Vec using (Vec)
open import Data.Bool using (Bool)
open import Data.Fin using (Fin)
```

## Boolean General Use
```

Nibble : Set
Nibble = Vec Bool 4

Byte : Set
Byte = Vec Bool 8

```

## ROM related
```
8KB : ℕ        -- size of the EEPROMs
8KB = 2 ^ 13

Address : Set
Address = Fin 8KB


```
