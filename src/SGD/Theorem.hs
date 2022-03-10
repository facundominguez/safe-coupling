{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--fast"           @-}
{-@ LIQUID "--ple-local"      @-}
{-@ LIQUID "--smttimeout=100000" @-}

module SGD.Theorem where

import           Prelude                 hiding ( head
                                                , tail
                                                , sum
                                                )
import           Language.Haskell.Liquid.ProofCombinators hiding ((=<=), (==.), (?))

import           Misc.ProofCombinators

import           Monad.Distr 
import           Monad.Distr.Laws
import           Monad.Distr.Relational.TCB.EDist
import           Monad.Distr.Relational.Theorems (bindDistEq)
import           Data.Dist 
import           SGD.SGD 
import           SGD.Lemmata.Helper





infixl 3 =<=
{- (=<=) :: x:Double -> y:{Double | x <= y} -> {v:Double | v == y} @-}
(=<=) :: Double -> Double -> Double
_ =<= y  = y

infixl 3 ?

(?) :: Double -> () -> Double 
x ? _ = x 


infixl 3 ==.
{- (=<=) :: x:Double -> y:{Double | x <= y} -> {v:Double | v == y} @-}
(==.) :: Double -> Double -> Double
_ ==. y  = y


{- ple thm @-}
{-@ thm :: d:Dist Double -> zs1:DataSet -> ws1:Weight -> α1:StepSizes -> f1:LossFunction -> 
           zs2:{DataSet | lend zs1 == lend zs2 && tail zs1 = tail zs2} -> 
            ws2:Weight -> {α2:StepSizes| α2 = α1} -> {f2:LossFunction|f1 = f2} -> 
            { dist (kant d) (sgd zs1 ws1 α1 f1) (sgd zs2 ws2 α2 f2) <= dist d ws1 ws2 + estab zs1 α1} / [sslen α1, 0]@-}
thm :: Dist Double -> DataSet -> Weight -> StepSizes -> LossFunction -> DataSet -> Weight -> StepSizes -> LossFunction -> ()
thm d zs1 ws1 α1@SSEmp f1 zs2 ws2 α2@SSEmp f2 =
  dist (kant d) (sgd zs1 ws1 α1 f1) (sgd zs2 ws2 α2 f2)
    ==. dist (kant d) (ppure ws1) (ppure ws2)
        ? pureDist d ws1 ws2
    ==. dist d ws1 ws2
        ? estabEmp zs1 
    ==. dist d ws1 ws2 + estab zs1 α1
    *** QED 

thm d zs1 ws1 as1@(SS α1 a1) f1 zs2 ws2 as2@(SS α2 a2) f2 
    =   dist (kant d) (sgd zs1 ws1 as1 f1) (sgd zs2 ws2 as2 f2)
    ==. dist (kant d) (bind (unif zs1) (sgdRecUpd zs1 ws1 α1 a1 f1)) 
                      (bind (unif zs2) (sgdRecUpd zs2 ws2 α2 a2 f2))
        ?   assert (unif zs1 == choice (1 `mydiv` lend zs1) (ppure z1) (unif zs1'))
        ?   assert (unif zs2 == choice (1 `mydiv` lend zs2) (ppure z2) (unif zs1'))
    ==. dist (kant d)
            (bind (choice p uhead1 utail1) sgdRec1)
            (bind (choice p uhead2 utail2) sgdRec2)
            ? choiceBind p uhead1 utail1 sgdRec1
            ? assert (utail1 == utail2)
       --  ? assert (bind (choice p uhead1 utail1) sgdRec1
       --      == choice p (bind uhead1 sgdRec1) (bind utail1 sgdRec1)
       --    )   
    ==. dist (kant d)
            (choice p (bind uhead1 sgdRec1) (bind utail1 sgdRec1))
            (bind (choice p uhead2 utail2) sgdRec2)
            ? choiceBind p uhead2 utail2 sgdRec2
            -- ? assert (bind (choice p uhead2 utail2) sgdRec2
            -- == choice p (bind uhead2 sgdRec2) (bind utail2 sgdRec2)
            -- ) 
    ==. dist (kant d)
          (choice p (bind uhead1 sgdRec1) (bind utail1 sgdRec1))
          (choice p (bind uhead2 sgdRec2) (bind utail2 sgdRec2))
        ?   choiceDist d p (bind uhead1 sgdRec1) (bind utail1 sgdRec1)
                    p (bind uhead2 sgdRec2) (bind utail2 sgdRec2)

    =<= p * (dist (kant d) (bind uhead1 sgdRec1) (bind uhead2 sgdRec2)) 
        + (1.0 - p) * (dist (kant d) (bind utail1 sgdRec1) (bind utail2 sgdRec2))
        ?   leftId z1 sgdRec1 
        ?   leftId z2 sgdRec2 

    =<= p * (dist (kant d) (sgdRec1 z1) (sgdRec2 z2)) 
        + q * (dist (kant d) (bind utail1 sgdRec1) (bind utail2 sgdRec2))
    
    =<= p * (dist (kant d) (bind (sgd zs1 ws1 a1 f1) pureUpd1) 
                                    (bind (sgd zs2 ws2 a2 f2) pureUpd2)) 
        + q * (dist (kant d) (bind utail1 sgdRec1) (bind utail2 sgdRec2))
            ? pureUpdateEq z1 α1 f1
            ? pureUpdateEq z2 α2 f2

    =<= p * (dist (kant d) (bind (sgd zs1 ws1 a1 f1) (ppure . update z1 α1 f1 )) 
                                    (bind (sgd zs2 ws2 a2 f2) (ppure . update z2 α2 f2 ))) 
        + q * (dist (kant d) (bind utail1 sgdRec1) (bind utail2 sgdRec2))

     ?   pureBindDist d d (2 * lip * α1) (update z1 α1 f1) (sgd zs1 ws1 a1 f1) 
                                    (update z2 α2 f2) (sgd zs2 ws2 a2 f2) 
                                    (relationalupdatep d z1 α1 f1 z2 α2 f2) 
        
    =<= p * (dist (kant d) (sgd zs1 ws1 a1 f1)  
                                    (sgd zs2 ws2 a2 f2) + (2.0 * lip * α1)) 
        + p * (dist (kant d) (bind utail1 sgdRec1) (bind utail2 sgdRec2))

         ? thm d zs1 ws1 a1 f1 zs2 ws2 a2 f2
         ? assert (dist (kant d) (sgd zs1 ws1 a1 f1) (sgd zs2 ws2 a2 f2) <= dist d ws1 ws2 + estab zs1 a1)
    =<= p * (dist d ws1 ws2 + estab zs1 a1 + (2.0 * lip * α1)) 
        + q * (dist (kant d) (bind utail1 sgdRec1) (bind utail2 sgdRec2))
        ? bindDistEq d (dist d ws1 ws2 + estab zs1 a1) sgdRec1 utail1 sgdRec2 utail2
                     (lemma d zs1 ws1 α1 a1 f1 zs2 ws2 α2 a2 f2)
        ? assert (dist (kant d) (bind utail1 sgdRec1) (bind utail2 sgdRec2) <= dist d ws1 ws2 + estab zs1 a1)
        ? assert (0 <= q)
        ? multHelper (p * (dist d ws1 ws2 + estab zs1 a1 + (2.0 * lip * α1))) q 
                 (dist (kant d) (bind utail1 sgdRec1) (bind utail2 sgdRec2))
                 (dist d ws1 ws2 + estab zs1 a1)
    =<= p * (dist d ws1 ws2 + estab zs1 a1 + (2.0 * lip * α1)) 
        + q * (dist d ws1 ws2 + estab zs1 a1)

    =<= p * (dist d ws1 ws2 + estab zs1 a1 + (2.0 * lip * α1)) 
            + q * (dist d ws1 ws2 + estab zs1 a1)

    =<= dist d ws1 ws2 + 2.0 * lip * α1 * p + estab zs1 a1
        ?   estabconsR zs1 α1 a1
                            
    =<= dist d ws1 ws2 + estab zs1 (SS α1 a1)
    =<= dist d ws1 ws2 + estab zs1 as1
    *** QED    {-  *** Admit  
-}
 where
     p = one / lend zs1
     q = 1.0 - p
     uhead1 = ppure z1
     uhead2 = ppure z2
     utail1 = unif zs1'
     utail2 = unif zs2'
     sgdRec1 = sgdRecUpd zs1 ws1 α1 a1 f1
     sgdRec2 = sgdRecUpd zs2 ws2 α2 a2 f2
     pureUpd1 = pureUpdate z1 α1 f1
     pureUpd2 = pureUpdate z2 α2 f2
     (z1:zs1'@(_:_)) = zs1 
     (z2:zs2'@(_:_)) = zs2
thm d zs1 ws1 _ f1 zs2 ws2 _ f2 = ()


{-@ lemma :: d:Dist Double -> zs1:DataSet -> ws1:Weight -> α1:StepSize -> a1:StepSizes -> f1:LossFunction -> 
             zs2:{DataSet | lend zs1 == lend zs2 && tail zs1 = tail zs2} -> 
             ws2:Weight -> α2:{StepSize | α1 = α2} -> {a2:StepSizes| a2 = a1} -> f2:{LossFunction|f1 = f2} ->  
             z:DataPoint -> 
             {dist (kant d) (sgdRecUpd zs1 ws1 α1 a1 f1 z) (sgdRecUpd zs2 ws2 α2 a2 f2 z) <= dist d ws1 ws2 + estab zs1 a1} / [sslen a1, 1] @-}
lemma :: Dist Double -> DataSet -> Weight -> StepSize -> StepSizes -> LossFunction -> DataSet -> Weight -> StepSize ->  StepSizes -> LossFunction -> DataPoint -> ()
lemma d zs1 ws1 α1 a1 f1 zs2 ws2 α2 a2 f2 z = 
  dist (kant d) (sgdRecUpd zs1 ws1 α1 a1 f1 z) (sgdRecUpd zs2 ws2 α2 a2 f2 z)
        ?   pureUpdateEq z α1 f1
        ?   pureUpdateEq z α2 f2
    ==. dist (kant d) (bind (sgd zs1 ws1 a1 f1) (pureUpdate z α1 f1)) 
                (bind (sgd zs2 ws2 a2 f2) (pureUpdate z α2 f2))
        ?   pureBindDist d d 0 (update z α1 f1) (sgd zs1 ws1 a1 f1)
                             (update z α2 f2) (sgd zs2 ws2 a2 f2) 
                             (relationalupdateq d z α1 f1 z α2 f2)
    =<= dist (kant d) (sgd zs1 ws1 a1 f1) (sgd zs2 ws2 a2 f2)
        ? thm d zs1 ws1 a1 f1 zs2 ws2 a2 f2
    =<= dist d ws1 ws2 + estab zs1 a1
    *** QED

