{-@ LIQUID "--reflection" @-}


module Monad.Distr where 

import Data.Dist (dist)

type Distr a = a
{-@ type Prob = {v:Double| 0 <= v && v <= 1} @-}
type Prob = Double

{-@ measure expDist :: Distr a -> Distr a -> Double @-}
{-@ assume expDist :: x1:_ -> x2:_ -> {v:Double | v == expDist x1 x2 } @-}
expDist :: Distr a -> Distr a -> Double
expDist _ _ = 0

{-@ assume relationalpbind :: e1:Distr a -> f1:(a -> Distr b) -> e2:Distr a -> f2:(a -> Distr b) -> 
        { expDist (pbind e1 f1) (pbind e2 f2) = expDist e1 e2 } @-}
relationalpbind :: Distr a  -> (a -> Distr b)  -> Distr a  -> (a -> Distr b) -> ()
relationalpbind = undefined

{-@ assume relationalqbind :: e1:Distr a -> f1:(a -> Distr b) -> {e2:Distr a | e1 = e2} -> f2:(a -> Distr b) -> 
        { expDist (qbind e1 f1) (qbind e2 f2) = expDist e1 e2} @-}
relationalqbind :: Distr a  -> (a -> Distr b)  -> Distr a  -> (a -> Distr b)  ->  ()
relationalqbind = undefined

{-@ measure Monad.Distr.pbind :: Distr a -> (a -> Distr b) -> Distr b @-}
{-@ assume pbind :: x1:Distr a -> x2:(a -> Distr b) -> {v:Distr b | v = pbind x1 x2 } @-}
pbind :: Distr a -> (a -> Distr b) -> Distr b
pbind = undefined

{-@ measure Monad.Distr.qbind :: Distr a -> (a -> Distr b) -> Distr b @-}
{-@ assume qbind :: x1:Distr a -> x2:(a -> Distr b) -> {v:Distr b | v = qbind x1 x2 } @-}
qbind :: Distr a -> (a -> Distr b) -> Distr b
qbind = undefined

{-@ assume relationalppure :: x1:a -> x2:a 
                    -> { expDist (ppure x1) (ppure x2) = dist x1 x2 } @-}
relationalppure :: a -> a -> () 
relationalppure _ _ = () 

{-@ measure Monad.Distr.ppure :: a -> Distr a @-}
{-@ ppure :: x:a -> {v:Distr a | v = ppure x } @-}
ppure :: a -> Distr a
ppure x = undefined

{-@ measure Monad.Distr.choice :: Prob -> Distr a -> Distr a -> Distr a @-}
{-@ assume choice :: x1:Prob -> x2:Distr a -> x3:Distr a -> {v:Distr a |  v == choice x1 x2 x3 } @-}
choice :: Prob -> Distr a -> Distr a -> Distr a
choice _ x _ = x

{-@ measure Monad.Distr.unif :: zs:[a] -> Distr a @-}
{-@ assume unif :: x:[a] -> {v:Distr a | v == unif x } @-}
unif :: [a] -> Distr a
unif _ = undefined
