module Ffi where

open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Data.Bool using (Bool)
open import Data.List using (List; _∷_; []; map; reverse)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Vec using (Vec; toList)
open import Function using (_∘_)
open import IO.Primitive

open import Common using (8KB; Byte; Address)

{-# FOREIGN GHC
  import qualified Data.Text.IO as Text
  import qualified System.IO as IO
  import qualified System.FilePath as FP
  import Data.Vector
  import Data.Word
  import Data.Bits
  import Data.ByteString
#-}

postulate FileHandle : Set
{-# COMPILE GHC FileHandle = type IO.Handle #-}

postulate FilePath : Set
{-# COMPILE GHC FilePath = type IO.FilePath #-}

postulate IOMode : Set
{-# COMPILE GHC IOMode = type IO.IOMode #-}

postulate Text : Set
{-# COMPILE GHC Text = type Data.Text.Text #-}

postulate Word8 : Set
{-# COMPILE GHC Word8 = type Data.Word.Word8 #-}

postulate ByteString : Set
{-# COMPILE GHC ByteString = type Data.ByteString.ByteString #-}

postulate
  stdout          : FileHandle
  hPutStrLn       : FileHandle → String → IO ⊤
  writeMode       : IOMode
  openFile        : FilePath → IOMode → IO FileHandle
  toFilePath      : String → FilePath
  hClose          : FileHandle → IO ⊤
  intToShow       : ℕ → String
  boolListToWord8 : List Bool → Word8
  pack            : List Word8 → ByteString
  hPut            : FileHandle → ByteString → IO ⊤

{-# COMPILE GHC stdout          = IO.stdout #-}
{-# COMPILE GHC hPutStrLn       = Text.hPutStrLn #-}
{-# COMPILE GHC openFile        = IO.openFile #-}
{-# COMPILE GHC writeMode       = IO.WriteMode #-}
{-# COMPILE GHC toFilePath      = Data.Text.unpack #-}
{-# COMPILE GHC hClose          = IO.hClose #-}
{-# COMPILE GHC intToShow       = Data.Text.pack . show #-}
{-# COMPILE GHC boolListToWord8 = \list -> ifoldr (\index bit byte -> if bit then setBit byte index else byte) (zeroBits :: Word8) (fromList list) #-}
{-# COMPILE GHC pack            = Data.ByteString.pack #-}
{-# COMPILE GHC hPut            = Data.ByteString.hPut #-}

toByteString : ∀ {n : ℕ} → Vec Byte n → ByteString
toByteString = pack ∘ map (boolListToWord8 ∘ reverse ∘ toList) ∘ toList

compile : ∀ {n : ℕ} → (Vec Byte n) × (Vec Byte n) → IO ⊤
compile ⟨ go-tos , signals ⟩ =
  openFile (toFilePath "go-to.bin") writeMode >>= λ goToFile →
  hPut goToFile (toByteString go-tos) >>= λ _ →
  hClose goToFile >>= λ _ →
  openFile (toFilePath "sig.bin") writeMode >>= λ sigFile →
  hPut sigFile (toByteString signals) >>= λ _ →
  hClose sigFile
