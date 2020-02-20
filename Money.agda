module Money where

import Agda.Builtin.IO as Builtin using (IO)
import Data.Rational as ℚ using (_+_; _*_)
open import Codata.Musical.Notation using (♯_)
open import Data.Nat using (ℕ; suc)
open import Data.Integer as ℤ using (+_)
open import Data.List using (List; []; _∷_)
open import Data.Rational as ℚ using (ℚ; 0ℚ; _/_)
open import Data.String using (String)
open import Data.Unit using (⊤)
open import Function using (_∘_) renaming (_$_ to _$$_)
open import IO using (putStrLn; IO; _>>_; run; sequence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Relation.Binary using (Decidable)
open import Relation.Nullary using (yes; no)
open import Codata.Musical.Colist as Colist using (fromList)
open Colist renaming (_∷_ to _::_)

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

mkSomeMoney : Currency → ℚ → SomeMoney
mkSomeMoney currency amount = record { currency = currency; money = mkMoney amount }

record Trade : Set where
  constructor mkTrade
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

_/1 : ℕ → ℚ
n /1 =  + n / 1

testTrades : List Trade
testTrades =
    mkTrade (mkSomeMoney £ (1 /1)) (100 /1)
  ∷ mkTrade (mkSomeMoney £ (2 /1)) (200 /1)
  ∷ mkTrade (mkSomeMoney $ (3 /1)) (300 /1)
  ∷ mkTrade (mkSomeMoney ¥ (5 /1)) (50 /1)
  ∷ []

open import Text.Printf using (printf)

showℚ : ℚ → String
showℚ record {numerator = n; denominator-1 = 0} = printf "%d" n
showℚ record {numerator = n; denominator-1 = d} = printf "%d/%u" n (suc d)

showCurrency : Currency → String
showCurrency € = "€"
showCurrency £ = "£"
showCurrency $ = "$"
showCurrency ¥ = "¥"

showMoney : {c : Currency} → Money c → String
showMoney {c} (mkMoney amount) = (printf "%s %s") (showCurrency c) (showℚ amount)

main : Builtin.IO (Colist ⊤)
main = run ∘ sequence ∘ fromList $$
    putStrLn "Hello, World!"
  ∷ putStrLn (showMoney $$ sumNotions {€} testTrades)
  ∷ putStrLn (showMoney $$ sumNotions {£} testTrades)
  ∷ putStrLn (showMoney $$ sumNotions {$} testTrades)
  ∷ putStrLn (showMoney $$ sumNotions {¥} testTrades)
  ∷ []
