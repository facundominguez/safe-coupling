-----------------------------------------------------------------
-- | Proved Theorems for Relational Properties: mapMSpec   ------
-----------------------------------------------------------------

{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}

module Monad.PrM.Relational.Theorems where 

import           Monad.PrM
import           Monad.PrM.Lift
import           Data.Dist
import           Data.List
import           Prelude hiding (max, mapM, const)

import           Monad.PrM.Relational.TCB.Spec 
import           Monad.PrM.Relational.TCB.EDist
import           Monad.PrM.Predicates

import           Language.Haskell.Liquid.ProofCombinators
import           Misc.ProofCombinators


-------------------------------------------------------
-- | bindDistEq when the bind args are BijCoupling  ---
-------------------------------------------------------

{-@ predicate BijCoupling X Y = X = Y @-}
{-@ bindDistEq :: Eq a => d:Dist b -> m:Double 
               -> f1:(a -> PrM b) -> e1:PrM a 
               -> f2:(a -> PrM b) -> e2:{PrM a | BijCoupling e1 e2 } 
               -> (x:a -> { dist (kant d) (f1 x) (f2 x) <= m}) 
               -> { dist (kant d) (bind e1 f1) (bind e2 f2) <= m } @-}
bindDistEq :: Eq a => Dist b -> Double -> (a -> PrM b) -> PrM a -> (a -> PrM b) ->  PrM a ->  (a -> ()) -> ()
bindDistEq d m f1 e1 f2 e2 lemma = 
  bindDist d m eqP f1 e1 f2 (e2 `const` liftSpec e2) 
          (makeTwoArg d m f1 f2 lemma)
   
{-@ makeTwoArg :: Eq a => d:Dist b -> m:Double -> f1:(a -> PrM b) -> f2:(a -> PrM b)
        -> (x:a -> {v:() | dist (kant d) (f1 x) (f2 x) <= m}) 
        -> (x:a -> y:{a | eqP x y} -> { dist (kant d) (f1 x) (f2 y) <= m}) @-} 
makeTwoArg :: Eq a => Dist b -> Double -> (a -> PrM b) -> (a -> PrM b) -> (a -> ())
    -> (a -> a -> ())
makeTwoArg d m f1 f2 lemma x y = lemma x  

-------------------------------------------------------
-- | mapM Spec ----------------------------------------
-------------------------------------------------------

{-@ annotate
      :: m:_
      -> f1:_
      -> f2:_
      -> xs:_
      -> p:{ lift (bounded m) (mapM f1 xs) (mapM f2 xs) }
      -> { r:_ | r = p && lift (bounded m) (mapM f1 xs) (mapM f2 xs) }
@-}
annotate :: Double -> (a -> PrM Double) -> (a -> PrM Double) -> List a -> () -> ()
annotate m f1 f2 xs p = p

{-@ proofMapMSpecNil :: xs:{ xs:_ | xs = [] } -> f1:_ -> { mapM f1 xs = ppure nilDouble } @-}
proofMapMSpecNil :: [a] -> (a -> PrM Double) -> ()
proofMapMSpecNil _ _ = ()

{-@ proofMapMSpecCons :: x:_ -> xs:_ -> f:_ -> { mapM f (cons x xs) = bind (f x) (consM (len xs) (mapM f xs)) } @-}
proofMapMSpecCons :: a -> [a] -> (a -> PrM Double) -> ()
proofMapMSpecCons _ _ _ = ()

{-@ lazy mapMSpec @-}
{-@ mapMSpec :: {m:Double|0 <= m} 
                   -> f1:(a -> PrM Double) -> f2:(a -> PrM Double) 
                   -> xs:[a]
                   -> (i:a -> {lift (bounded' m) (f1 i) (f2 i)}) 
                   -> {lift (bounded m) (mapM f1 xs) (mapM f2 xs)} @-}
mapMSpec :: Double -> (a -> PrM Double) -> (a -> PrM Double) -> List a 
               -> (a -> ()) 
               -> ()
mapMSpec m f1 f2 xs lemma = case xs of
      [] -> annotate m f1 f2 xs (pureSpec (bounded m) nilDouble nilDouble (boundedNil m) ? proofMapMSpecNil xs f1 ? proofMapMSpecNil xs f2)
      i:is -> annotate m f1 f2 xs (bindSpec (bounded m) (bounded' m)
            (f1 i) (consM (len is) (mapM f1 is))
            (f2 i) (consM (len is) (mapM f2 is))
            (lemma i)
            (consBindLemma m f1 f2 is lemma)  ? proofMapMSpecCons i is f1 ? proofMapMSpecCons i is f2)

{-@ consLemma :: m:Double -> r1:Double -> rs1:List Double -> {r2:Double|bounded' m r1 r2} 
              -> {rs2:List Double|len rs1 = len rs2 && bounded m rs1 rs2} 
              -> {bounded m (consDouble r1 rs1) (consDouble r2 rs2)} @-}
consLemma :: Double -> Double -> List Double -> Double -> List Double -> ()
consLemma m r1 rs1 r2 rs2 = ()

{-@ lazy consBindLemma @-}
{-@ consBindLemma :: {m:Double|0 <= m} -> f1:(a -> PrM Double) -> f2:(a -> PrM Double) 
                  -> xs:[a] 
                  -> (i:a -> {lift (bounded' m) (f1 i) (f2 i)})
                  -> r1:Double
                  -> {r2:Double|bounded' m r1 r2}
                  -> {lift (bounded m) 
                           ((consM (len xs) (mapM f1 xs)) (r1)) 
                           ((consM (len xs) (mapM f2 xs)) (r2))} / [len xs, 1] @-}
consBindLemma :: Double -> (a -> PrM Double) -> (a -> PrM Double) 
              -> [a] 
              -> (a -> ()) 
              -> Double -> Double
              -> ()
consBindLemma m f1 f2 is lemma r1 r2
    = bindSpec (bounded m) (bounded m)
                         (mapM f1 is) (ppure `o` (consDouble r1))
                         (mapM f2 is) (ppure `o` (consDouble r2))
                         (mapMSpec m f1 f2 is lemma)
                         (pureLemma m r1 r2 f1 f2 is)

{-@ pureLemma :: {m:Double|0 <= m} 
           -> r1:Double -> {r2:Double|bounded' m r1 r2}  
           -> f1:(a -> PrM Double) -> f2:(a -> PrM Double) -> is:List a 
           -> rs1:List Double -> rs2:{List Double|bounded m rs1 rs2}
           -> {lift (bounded m) (o ppure (consDouble r1) rs1)
                                (o ppure (consDouble r2) rs2)} @-}
pureLemma :: Double -> Double -> Double -> (a -> PrM Double) -> (a -> PrM Double) 
       -> List a -> List Double -> List Double -> () 
pureLemma m r1 r2 f1 f2 is rs1 rs2 | len rs1 == len rs2 
    = pureSpec (bounded m) 
        (consDouble r1 rs1) (consDouble r2 rs2) 
        (consLemma m r1 rs1 r2 rs2)
pureLemma m r1 r2 f1 f2 is rs1 rs2 = ()

{-@ boundedNil :: {m:Double|0 <= m} -> {bounded m nilDouble nilDouble} @-}
boundedNil :: Double -> ()
boundedNil _ = ()

{-@ unifChoice :: x:a -> {xs:[a]|1 <= len xs} 
               -> {unif (cons x xs) = choice (mydiv 1.0 (lend (cons x xs))) (ppure x) (unif xs)} @-}
unifChoice :: a -> [a] -> ()
unifChoice x xs@(_:_) 
  = case cons x xs of 
        [] -> ()
        [a] -> ()
        (y:ys) -> unif (cons x xs) === unif (y:ys) 
                   ===  choice (1.0 `mydiv` lend (cons x xs)) (ppure y) (unif ys) *** QED 

{-@ unifPermut :: Eq a => Dist a -> {xs1:[a]|1 <= len xs1} -> {xs2:[a]|1 <= len xs2 && isPermutation xs1 xs2} -> {unif xs1 = unif xs2} @-}
unifPermut :: Eq a => Dist a -> [a] -> [a] -> ()
unifPermut d xs1 xs2 | isPermutation xs1 xs2 && 1 <= len xs1 && 1 <= len xs2 
    = ()
        ? unifDist d xs1 xs2
        ? assert (kdist d (unif xs1) (unif xs2) == 0)
        ? distEq (kant d) (unif xs1) (unif xs2)
        ? assert ((unif xs1) == (unif xs2))
unifPermut _ _ _ = ()

{-@ permutLen :: Eq a => xs:[a] -> ys:[a] -> {isPermutation xs ys => len xs = len ys} @-}
permutLen :: Eq a => [a] -> [a] -> ()
permutLen xs ys = () ? isPermutation xs ys