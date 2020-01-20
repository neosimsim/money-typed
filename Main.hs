{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE EmptyCase                  #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}

module Main
  ( main
  ) where

import           Data.Singletons.TH

$(singletons
    [d|

  data Currency = EUR
                | GBP
                | USD
                | JPY
                    deriving (Show, Eq)
  |])

newtype Money (currency :: Currency) =
  Money
    { unMoney :: Rational
    }
  deriving newtype (Show)

plus :: Money c -> Money c -> Money c
plus (Money v1) (Money v2) = Money $ v1 + v2

multiply :: Money c -> Rational -> Money c
multiply (Money v1) x = Money $ v1 * x

data SomeMoney =
  forall c. SomeMoney (SCurrency c) (Money c)

instance Show SomeMoney where
  show (SomeMoney c m) =
    "SomeMoney " ++ show (fromSing c) ++ " " ++ show (unMoney m)

mkSomeMoney :: SCurrency c -> Rational -> SomeMoney
mkSomeMoney sCurrency amount = SomeMoney sCurrency (Money amount)

newtype Ticker =
  Ticker String
  deriving newtype (Show)

data Trade =
  Trade
    { tQty    :: Rational
    , tPrice  :: SomeMoney
    , tTicker :: Ticker
    }
  deriving (Show)

testTrades :: [Trade]
testTrades =
  [ Trade 100 (mkSomeMoney SGBP 1) (Ticker "VOD.L")
  , Trade 200 (mkSomeMoney SGBP 2) (Ticker "VOD.L")
  , Trade 300 (mkSomeMoney SUSD 3) (Ticker "AAPL.L")
  , Trade 50 (mkSomeMoney SJPY 5) (Ticker "4151.T")
  ]

-- | Sum notionals over all trades with a given currency.
sumNotionals :: SCurrency c -> [Trade] -> Money c
sumNotionals _ [] = Money 0
sumNotionals sCurrency (t:ts) =
  case tPrice t of
    SomeMoney priceSCurrencry money ->
      case sCurrency %~ priceSCurrencry of
        Proved Refl -> multiply money (tQty t) `plus` sumNotionals sCurrency ts
        Disproved _ -> sumNotionals sCurrency ts

-- | @sumNotionals@ but with currency implicitly given.
sumNotionals' ::
     forall c. SingI c
  => [Trade]
  -> Money c
sumNotionals' [] = Money 0
sumNotionals' (t:ts) =
  case tPrice t of
    SomeMoney priceSCurrencry money ->
      case priceSCurrencry %~ sing @c of
        Proved Refl -> multiply money (tQty t) `plus` sumNotionals' ts
        Disproved _ -> sumNotionals' ts

main :: IO ()
main = do
  putStrLn "Hello, Haskell!"
  print $ SomeMoney SEUR (Money 10.3)
  print $ sumNotionals SEUR testTrades
  print $ sumNotionals SGBP testTrades
  print $ sumNotionals SUSD testTrades
  print $ sumNotionals SJPY testTrades
  print $ sumNotionals' @'JPY testTrades
