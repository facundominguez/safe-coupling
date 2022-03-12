{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}

module TD.Lemmata.Relational.Iterate where 

import           Monad.PrM
import           Data.Dist
import           Data.List
import           Prelude hiding (iterate)

import           Monad.PrM.Relational.TCB.Spec 
import           Monad.PrM.Predicates

import           TD.TD0 
import           Language.Haskell.Liquid.ProofCombinators
import           Misc.ProofCombinators


{-@ relationaliterate :: m:{_|0 <= m} -> {k:_|k >= 0} -> n:Nat -> l:Nat
                      -> f:(v:ListN l -> PrM (ListN l))
                      -> (m:{_|0 <= m} -> y1:{List Double|llen y1 = l} -> y2:{List Double|llen y2 = l} -> {bounded m y1 y2 => lift (bounded (k * m)) (f y1) (f y2)})
                      -> x1:ListN l -> x2:ListN l
                      -> {bounded m x1 x2 => lift (bounded (pow k n * m)) ((iterate n (llen x1) f) (x1)) 
                                                                          ((iterate n (llen x2) f) (x2))} / [n] @-}
relationaliterate :: Double -> Double -> Int -> Int
                  -> (List Double -> PrM (List Double)) 
                  -> (Double -> List Double -> List Double -> ()) 
                  -> List Double -> List Double
                  -> ()
relationaliterate m k 0 _ _ _ x1 x2 | bounded m x1 x2
    =   pureSpec (bounded (pow k 0 * m)) x1 x2 ()
relationaliterate m k n l f lemma x1 x2 | bounded m x1 x2
    =   assert (pow k (n-1) * (k * m) == pow k n * m) ? 
        bindSpec (bounded (pow k n * m)) (bounded (k * m)) 
                 (f x1) (iterate (n - 1) (llen x1) f)
                 (f x2) (iterate (n - 1) (llen x2) f)
                 (lemma m x1 x2)
                 (relationaliterate (k * m) k (n - 1) l f lemma)
relationaliterate m k n l f lemma x1 x2 = ()
