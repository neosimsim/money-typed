module Money where

open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.String
open import Data.Rational as ℚ using (ℚ; 0ℚ; _/_)
import Data.Rational as ℚ using (_+_; _*_)
open import Data.List
open import Data.Integer as ℤ using (+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary using (Decidable)


data Currency : Set where
  € : Currency
  £ : Currency
  $ : Currency
  ¥ : Currency

data Money : Currency → Set where
  mkMoney : {c : Currency} → ℚ → Money c

noMoney : Money $
noMoney = mkMoney (+ 0 / 1)

_+_ : {c : Currency} → Money c → Money c → Money c
mkMoney x₁ + mkMoney x₂ =  mkMoney (x₁ ℚ.+ x₂)
infix 30 _+_

_*_ : {c : Currency} → ℚ → Money c → Money c
x * mkMoney y = mkMoney (x ℚ.* y)

record SomeMoney : Set where
  field
    currency : Currency
    money : Money currency

record Trade : Set where
  field
    tPrice : SomeMoney
    tQty : ℚ

data Equal? (c₁ c₂ : Currency) : Set where
  eq : c₁ ≡ c₂ → Equal? c₁ c₂
  neq : c₁ ≢ c₂ → Equal? c₁ c₂



infix 4 _≟_
_≟_ : Decidable {A = Currency} _≡_
€ ≟ € = yes refl
€ ≟ £ = no (λ ())
€ ≟ $ = no (λ ())
€ ≟ ¥ = no (λ ())
£ ≟ € = no (λ ())
£ ≟ £ = yes refl
£ ≟ $ = no (λ ())
£ ≟ ¥ = no (λ ())
$ ≟ € = no (λ ())
$ ≟ £ = no (λ ())
$ ≟ $ = yes refl
$ ≟ ¥ = no (λ ())
¥ ≟ € = no (λ ())
¥ ≟ £ = no (λ ())
¥ ≟ $ = no (λ ())
¥ ≟ ¥ = yes refl

sumNotions : {c : Currency} → List Trade → Money c
sumNotions [] = mkMoney 0ℚ
sumNotions {c} (record { tPrice = record { currency = currency; money = money }; tQty = tQty } ∷ xs) with  c ≟ currency
... | yes refl = (tQty * money) +  sumNotions xs
... | no _ = sumNotions xs


postulate
  putStrLn : String → IO ⊤

{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# COMPILE GHC putStrLn = Text.putStrLn #-}

main : IO ⊤
main = putStrLn "Hello, World!"
