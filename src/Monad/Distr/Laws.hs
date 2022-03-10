-----------------------------------------------------------------
-- | Monad Laws for the Distr monad -----------------------------
-----------------------------------------------------------------

{-@ LIQUID "--reflection"  @-}
module Monad.Distr.Laws where 

import Monad.Distr

{-@ assume leftId :: x:a -> f:(a -> Distr b) -> { bind (ppure x) f = f x } @-}
leftId :: a -> (a -> Distr b) -> ()
leftId _ _ = ()

{-@ assume choiceBind :: p:Prob -> e1:Distr a -> e2:Distr a -> f:(a -> Distr b) 
                      -> {choice p (bind e1 f) (bind e2 f) = bind (choice p e1 e2) f} @-}
choiceBind :: Prob -> Distr a -> Distr a -> (a -> Distr b) -> ()
choiceBind _ _ _ _ = ()

{-@ assume commutative :: e:Distr a -> u:Distr b -> f:(a -> b -> Distr c) 
                -> {bind e (seqBind u f)
                      = bind u (seqBind e (flip f))} @-}
commutative :: Distr a -> Distr b -> (a -> b -> Distr c) -> ()
commutative _ _ _ = ()