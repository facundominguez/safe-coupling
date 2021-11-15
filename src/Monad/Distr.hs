{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple-local"     @-}

module Monad.Distr where 

import Data.Dist (dist)

newtype Distr a = Distr a


{-@ assume expDistPure :: x1:a -> x2:a -> {expDist (ppure x1) (ppure x2) = dist x1 x2} @-}
expDistPure :: a -> a -> ()
expDistPure _ _ = ()

{-@ assume expDistEq :: x1:Distr a -> {x2:Distr a | x1 = x2 } -> {expDist x1 x2 = 0} @-}
expDistEq :: Distr a -> Distr a -> ()
expDistEq _ _ = ()


-- CHECK IF THIS IS CORRECT 
{-@ ple relUnitBindTry @-}
{-@ assume relUnitBindTry :: m:Double 
                          -> f1:(a -> b) -> e1:Distr a 
                          -> f2:(a -> b) -> e2:Distr a 
                          -> (x1:a -> x2:a -> { dist (f1 x1) (f2 x2) <= dist x1 x2 + m}) 
                          -> { expDist (bind e1 (ppure . f1 )) (bind e2 (ppure . f2)) <= expDist e1 e2 + m } @-}
relUnitBindTry :: Double -> (a -> b) -> Distr a -> (a -> b) ->  Distr a ->  (a -> a -> ()) -> ()
relUnitBindTry m f1 e1 f2 e2 t = () --  maxExpDistLemma e1 e2 `const` relUnitBind m f1 e1 f2 e2 t


{-@ assume relUnitBind :: m:Double 
                          -> f1:(a -> b) -> e1:Distr a 
                          -> f2:(a -> b) -> e2:Distr a 
                          -> (x1:a -> x2:a -> { dist (f1 x1) (f2 x2) <= dist x1 x2 + m}) 
                          -> { expDist (bind e1 (ppure . f1 )) (bind e2 (ppure . f2)) <= maxExpDist e1 e2 + m } @-}
relUnitBind :: Double -> (a -> b) -> Distr a -> (a -> b) ->  Distr a ->  (a -> a -> ()) -> ()
relUnitBind _ _ _ _ _ _ = ()



{-@ assume expDistBind :: m:Double 
                          -> f1:(a -> Distr b) -> e1:Distr a 
                          -> f2:(a -> Distr b) -> e2:{Distr a | BijCoupling e1 e2 } 
                          -> (x:a -> { expDist (f1 x) (f2 x) <= m}) 
                          -> { expDist (bind e1 f1) (bind e2 f2) <= m } @-}
expDistBind :: Double -> (a -> Distr b) -> Distr a -> (a -> Distr b) ->  Distr a ->  (a -> ()) -> ()
expDistBind _ _ _ _ _ _ = ()


-------------------------------------------------------------------------------
-- | (Non) Definitions --------------------------------------------------------
-------------------------------------------------------------------------------

{-@ predicate BijCoupling X Y = X == Y @-}

{-@ type Prob = {v:Double| 0 <= v && v <= 1} @-}
type Prob = Double


{-@ assume maxExpDistLemma :: x1:Distr a -> x2:Distr a -> { expDist x1 x2 <=  maxExpDist x1 x2 } @-}
maxExpDistLemma :: Distr a -> Distr a -> ()
maxExpDistLemma _ _ = ()


{-@ measure maxExpDist :: Distr a -> Distr a -> Double @-}
{-@ assume maxExpDist :: x1:Distr a -> x2:Distr a -> {v:Double | v == maxExpDist x1 x2 } @-}
maxExpDist :: Distr a -> Distr a -> Double
maxExpDist _ _ = 0


{-@ measure expDist :: Distr a -> Distr a -> Double @-}
{-@ assume expDist :: x1:Distr a -> x2:Distr a -> {v:Double | v == expDist x1 x2 } @-}
expDist :: Distr a -> Distr a -> Double
expDist _ _ = 0

-------------------------------------------------------------------------------
-- | Relational Specifications ------------------------------------------------
-------------------------------------------------------------------------------
{-@ assume relationalppure :: x1:a -> x2:a 
                    -> { expDist (ppure x1) (ppure x2) = dist x1 x2 } @-}
relationalppure :: a -> a -> () 
relationalppure _ _ = () 

{-@ assume leftId :: x:a -> f:(a -> Distr b) -> { bind (ppure x) f = f x } @-}
leftId :: a -> (a -> Distr b) -> ()
leftId _ _ = ()

{-@ assume relationalchoice :: p:Prob -> e1:Distr a -> e1':Distr a 
        ->  q:{Prob | p = q } -> e2:Distr a -> e2':Distr a 
        ->  { expDist (choice p e1 e1') (choice q e2 e2') <= p * (expDist e1 e2) + (1.0 - p) * (expDist e1' e2')} @-}
relationalchoice :: Prob -> Distr a -> Distr a -> Prob -> Distr a -> Distr a -> ()
relationalchoice _ _ _ _ _ _ = ()

-------------------------------------------------------------------------------
-- | (Non) Implementations ----------------------------------------------------
-------------------------------------------------------------------------------

{-@ measure Monad.Distr.bind :: Distr a -> (a -> Distr b) -> Distr b @-}
{-@ assume bind :: x1:Distr a -> x2:(a -> Distr b) -> {v:Distr b | v = bind x1 x2 } @-}
bind :: Distr a -> (a -> Distr b) -> Distr b
bind = undefined

{-@ measure Monad.Distr.pbind :: Distr a -> (a -> Distr b) -> Distr b @-}
{-@ assume pbind :: x1:Distr a -> x2:(a -> Distr b) -> {v:Distr b | v = pbind x1 x2 } @-}
pbind :: Distr a -> (a -> Distr b) -> Distr b
pbind = undefined

{-@ measure Monad.Distr.qbind :: Distr a -> (a -> Distr b) -> Distr b @-}
{-@ assume qbind :: x1:Distr a -> x2:(a -> Distr b) -> {v:Distr b | v = qbind x1 x2 } @-}
qbind :: Distr a -> (a -> Distr b) -> Distr b
qbind = undefined

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
