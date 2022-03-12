{-@ LIQUID "--reflection"     @-}
{-@ LIQUID "--ple"            @-}

module SGD.Lemmata.Helper where

import           Prelude                 hiding ( head
                                                , tail
                                                , sum
                                                )
import           Language.Haskell.Liquid.ProofCombinators 

import           Misc.ProofCombinators 

import           Monad.Distr 
import           Monad.Distr.Laws
import           Monad.Distr.Relational.TCB.EDist
import           Monad.Distr.Relational.Theorems (bindDistEq)
import           Data.Dist 
import           SGD.SGD 


{-@ assume relationalupdatep :: d:Dist Double -> z1:DataPoint -> α1:StepSize -> f1:LossFunction 
                             -> z2:DataPoint -> {α2:StepSize|α1 = α2} -> {f2:LossFunction|f1 = f2} 
                             -> ws1:Weight -> ws2:Weight -> 
                            {dist d (update z1 α1 f1 ws1) (update z2 α2 f2 ws2) = dist d ws1 ws2 + 2.0 * lip * α1 } @-}
relationalupdatep :: Dist Double -> DataPoint -> StepSize -> LossFunction -> DataPoint -> StepSize -> LossFunction -> Weight  -> Weight -> ()
relationalupdatep _ _ _ _ _ _ _ _ _ = ()


{-@ assume relationalupdateq :: d:Dist Double -> z1:DataPoint -> α1:StepSize -> f1:LossFunction 
                             -> {z2:DataPoint|z1 = z2} -> {α2:StepSize|α1 = α2} -> {f2:LossFunction|f1 = f2} 
                             -> ws1:Weight -> ws2:Weight -> 
                            {dist d (update z1 α1 f1 ws1) (update z2  α2 f2 ws2) = dist d ws1 ws2} @-}
relationalupdateq :: Dist Double -> DataPoint -> StepSize -> LossFunction -> DataPoint -> StepSize -> LossFunction -> Weight  -> Weight -> ()
relationalupdateq _ _ _ _ _ _ _ _ _ = () 



{-@ measure SGD.Lemmata.Helper.lip :: Double @-}
{-@ assume lip :: {v:Double|SGD.Lemmata.Helper.lip = v && v >= 0 } @-}
lip :: Double
lip = 10

{-@ reflect sum @-}
{-@ sum :: StepSizes -> {v:StepSize | 0.0 <= v } @-}
sum :: StepSizes -> Double
sum SSEmp       = 0
sum (SS a as) = a + sum as

{-@ reflect estab @-}
{-@ estab :: DataSet -> StepSizes -> {v:Double | 0.0 <= v} @-}
estab :: DataSet -> StepSizes -> Double
estab zs as = 2.0 * lip / (lend zs) * sum as

{-@ ple estabEmp @-}
estabEmp :: DataSet -> () 
{-@ estabEmp :: zs:DataSet -> {estab zs SSEmp == 0.0} @-}
estabEmp zs = 
      estab zs SSEmp 
  ==. 2.0 / (lend zs) * sum SSEmp
  *** QED 

{-@ ple estabconsR @-}
{-@ measure SGD.Lemmata.Helper.estabconsR  :: DataSet -> StepSize -> StepSizes -> ()  @-}
{-@ estabconsR :: zs:{DataSet | lend zs /= 0} -> x:StepSize -> xs:StepSizes 
                    -> { estab zs (SS x xs) == 2.0 * lip * x * (one / lend zs) + estab zs xs } @-}
estabconsR :: DataSet -> StepSize -> StepSizes -> () 
estabconsR zs x xs 
  =   estab zs (SS x xs)
  ==. 2.0 * lip / (lend zs) * sum (SS x xs)
  ==. 2.0 * lip * x * (one / lend zs) + estab zs xs 
  *** QED 



{-@ multHelper :: a:Double -> b:{Double | 0 <= b} -> c:Double -> d:{Double | c <= d } 
               -> { a + b * c <= a + b * d }  @-}
multHelper :: Double -> Double -> Double -> Double -> () 
multHelper _ _ _ _ = ()





{-@ assume pureUpdateEq :: zs:DataPoint -> a:StepSize -> f:LossFunction
               -> {pureUpdate zs a f == ppure . update zs a f} @-}
pureUpdateEq :: DataPoint -> StepSize -> LossFunction -> ()
pureUpdateEq zs a f = () 
