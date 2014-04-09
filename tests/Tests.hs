{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE FlexibleContexts #-}

import Test.Tasty (TestName, TestTree, defaultMain, localOption, testGroup)
import Test.Tasty.QuickCheck hiding ((.&.))

import Data.Bits (Bits(..))
import Data.Int
import Data.Word
import Data.BinaryWord

main ∷ IO ()
main = defaultMain
     $ localOption (QuickCheckTests 10000)
     $ testGroup "Tests"
         [ binWordGroup "Word8" (0 ∷ Word8)
         , binWordGroup "Word16" (0 ∷ Word16)
         , binWordGroup "Word32" (0 ∷ Word32)
         , binWordGroup "Word64" (0 ∷ Word64)
         , binWordGroup "Int8" (0 ∷ Int8)
         , binWordGroup "Int16" (0 ∷ Int16)
         , binWordGroup "Int32" (0 ∷ Int32)
         , binWordGroup "Int64" (0 ∷ Int64)
         ]

sameType ∷ α → α → α
sameType = const id

binWordGroup ∷ (Show w, Arbitrary w, Integral w, Integral (UnsignedWord w),
                BinaryWord w) ⇒ TestName → w → TestTree
binWordGroup n w = testGroup n
  [ testProperty "allZeroes" $ popCount (sameType w allZeroes) == 0
  , testProperty "allOnes" $ popCount (sameType w allOnes) == bitSize w
  , testProperty "unwrappedAdd" $ \w₁ w₂ →
      let (h, l) = unwrappedAdd (sameType w w₁) w₂ in
        toInteger h * 2 ^ bitSize w + toInteger l ==
          toInteger w₁ + toInteger w₂
  , testProperty "unwrappedMul" $ \w₁ w₂ →
      let (h, l) = unwrappedMul (sameType w w₁) w₂ in
        toInteger h * 2 ^ bitSize w + toInteger l ==
          toInteger w₁ * toInteger w₂
  ]
