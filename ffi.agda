open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import IO.Primitive
open import Codata.Musical.Notation

{-# FOREIGN GHC
  import qualified Data.Text.IO as Text
  import qualified System.IO as IO
  import qualified System.FilePath as FP
#-}

postulate FileHandle : Set
{-# COMPILE GHC FileHandle = type IO.Handle #-}

postulate FilePath : Set
{-# COMPILE GHC FilePath = type IO.FilePath #-}

postulate IOMode : Set
{-# COMPILE GHC IOMode = type IO.IOMode #-}

postulate Text : Set
{-# COMPILE GHC Text = type Data.Text.Text #-}

postulate
  stdout       : FileHandle
  hPutStrLn : FileHandle → String → IO ⊤
  writeMode    : IOMode
  openFile : FilePath → IOMode → IO FileHandle
  addExtension : FilePath → String → FilePath
  foo : String → FilePath
  hClose : FileHandle → IO ⊤

{-# COMPILE GHC stdout = IO.stdout #-}
{-# COMPILE GHC hPutStrLn = Text.hPutStrLn #-}
{-# COMPILE GHC openFile = IO.openFile #-}
{-# COMPILE GHC writeMode = IO.WriteMode #-}
{-# COMPILE GHC addExtension = \x y -> FP.addExtension x (Data.Text.unpack y) #-}
{-# COMPILE GHC foo = \x -> Data.Text.unpack x #-}
{-# COMPILE GHC hClose = IO.hClose #-}

main =
  openFile (addExtension (foo "out") "txt") writeMode >>= λ file →
  hPutStrLn file "Hello, world!"                      >>= λ _    →
  hClose file
