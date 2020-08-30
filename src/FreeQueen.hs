{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE EmptyCase         #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE InstanceSigs      #-}
{-# LANGUAGE PolyKinds         #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}

module FreeQueen where

import           Control.Monad.IO.Class     (MonadIO (liftIO))
import           Control.Monad.State.Strict (StateT, execStateT, get, modify,
                                             put, runStateT)
import           Control.Monad.Trans        (lift)
import           Control.Monad.Trans.Maybe
import           Data.List                  (intercalate, reverse)
import           Text.Read                  (readMaybe)

----------------
-- With GADTs --
----------------

data Free f a where
    Pure :: a -> Free f a
    Step :: f a -> (a -> Free f b) -> Free f b

pure :: a -> Free f a
pure = Pure

alg :: f (Free f a) ->  Free f a
alg more = Step more id

liftF :: Functor f => f a -> Free f a
liftF = alg . fmap Pure

instance Functor (Free f) where
  fmap :: (a -> b) -> Free f a -> Free f b
  fmap function (Pure x)       = Pure $ function x
  fmap function (Step fa cont) = Step fa (fmap function . cont)

instance Applicative (Free f) where
    pure = Pure
    Pure f <*> x = fmap f x
    Step fa cont <*> x = Step fa ((<*> x) . cont)

instance Monad (Free f) where
  return = Pure
  Pure x >>= f = f x
  (Step fa cont) >>= f = Step fa ((>>= f) . cont)

foldFree :: (Functor f, Monad m) => (forall x . f x -> m x) -> Free f a -> m a
foldFree _ (Pure x)     = return x
foldFree a (Step fa cc) = a (fmap cc fa) >>= foldFree a

------------------
-- Permutations --
------------------

data Empty

data Command a where
    Fail :: Command Empty
    Choice :: Command Bool

type ND = Free Command

never :: Empty -> a
never x = case x of { }

fail :: ND a
fail = Step Fail never

choice :: ND a -> ND a -> ND a
choice c1 c2 = Step Choice (\b -> if b then c1 else c2)

permutations :: [a] -> ND [a]
permutations []     = Pure []
permutations (x:xs) = permutations xs >>= insert x

insert :: a -> [a] -> ND [a]
insert x [] = return [x]
insert x (y:ys) = choice (return (x:y:ys))
                         (do partial <- insert x ys
                             return (y : partial))

run :: ND a -> [a]
run (Pure a)        = [a]
run (Step Fail _)   = []
run (Step Choice k) = run (k True) ++ run (k False)


-------------
-- nQueens --
-------------

data Commands a where
  Failure :: Commands Empty
  Choices :: Int -> Commands Int

type NonDet = Free Commands

failure :: NonDet a
failure = Step Failure never

class HasEmpty f where
  emptyValue :: f a

guard :: (HasEmpty f, Applicative f) => Bool -> f ()
guard True  = Prelude.pure ()
guard False = emptyValue

instance HasEmpty NonDet where
  emptyValue = failure

choices :: Int -> (Int -> NonDet a) -> NonDet a
choices = Step . Choices

newtype Queens = Queens {unQueens :: [Int]}
  deriving (Show, Eq, Semigroup, Monoid)

nQueens :: Int -> NonDet Queens
nQueens n = nQueensAcc n n

nQueensAcc :: Int -> Int -> NonDet Queens
nQueensAcc n 0 = Pure (Queens [])
nQueensAcc n k = nQueensAcc n (k - 1) >>= addQueen n

addQueen :: Int -> Queens -> NonDet Queens
addQueen n = choices n . chooseQueen n

chooseQueen :: Int -> Queens -> Int -> NonDet Queens
chooseQueen n (Queens qs) k = do guard (check qs k)
                                 return (Queens (k : qs))

check :: [Int] -> Int -> Bool
check qs k = k `notElem` qs && checkDiagonal qs 1
          where checkDiagonal [] _ = True
                checkDiagonal (x:xs) acc = x /= k - acc
                                        && x /= k + acc
                                        && checkDiagonal xs (acc + 1)

prettyPrintQueens :: Queens -> String
prettyPrintQueens = intercalate "\n"
                  . fmap (\n -> replicate n ' ' ++ "x")
                  . reverse
                  . unQueens

runNonDet :: NonDet a -> [a]
runNonDet (Pure x)              = [x]
runNonDet (Step Failure _)      = []
runNonDet (Step (Choices n) cs) = foldChoices (++) [] (runNonDet . cs) n

foldChoices :: (a -> b -> b) -> b -> (Int -> a) -> Int -> b
foldChoices op start as 0 = start
foldChoices op start as k = foldChoices op (op (as (k - 1)) start) as (k - 1)

runQueens :: Int -> IO ()
runQueens = putStrLn
          . intercalate "\n\n"
          . runNonDet
          . fmap prettyPrintQueens
          . nQueens

-------------------
-- Without GADTs --
-------------------

data Free' f a
  = Pure' a
  | Free' (f (Free' f a))

instance Functor f => Functor (Free' f) where
  fmap :: (a -> b) -> Free' f a -> Free' f b
  fmap function (Pure' a)    = Pure' (function a)
  fmap function (Free' more) = Free' $ fmap (fmap function) more

instance Functor f => Applicative (Free' f) where
  pure :: a -> Free' f a
  pure = Pure'

  (<*>) :: Free' f (a -> b) -> Free' f a -> Free' f b
  (Pure' function) <*> x = fmap function x
  (Free' moreFunction) <*> x = Free' $ fmap (<*> x) moreFunction

instance Functor f => Monad (Free' f) where
  return :: a -> Free' f a
  return = Pure'

  (>>=) :: Free' f a -> (a -> Free' f b) -> Free' f b
  Pure' a >>= f = f a
  (Free' more) >>= f = Free' $ fmap (>>= f) more


liftF' :: Functor f => f a -> Free' f a
liftF' = Free' . fmap Pure'

foldFree' :: Monad m => (forall x . f x -> m x) -> Free' f a -> m a
foldFree' _ (Pure' a)  = return a
foldFree' f (Free' as) = f as >>= foldFree' f

--------------------------------
-- Permutations without GADTs --
--------------------------------

data Command' a = Fail' | Choice' (Bool -> ND' a)
    deriving Functor

type ND' a = Free' Command' a

fail' :: ND' a
fail' = liftF' Fail'

choice' :: ND' a -> ND' a -> ND' a
choice' c1 c2  = liftF' $ Choice' (\b -> if b then c1 else c2)

permutations' :: [a] -> ND' [a]
permutations' []     = Pure' []
permutations' (x:xs) = permutations' xs >>= insert' x

insert' :: a -> [a] -> ND' [a]
insert' x [] = return [x]
insert' x (y:ys) = choice' (return (x:y:ys))
                           (do partial <- insert' x ys
                               return (y:partial))

runF' :: Command' a -> [a]
runF' Fail'        = []
runF' (Choice' xs) = run' (xs True) ++ run' (xs False)

run' :: ND' a -> [a]
run' = foldFree' runF'

--------------------------
-- nQueens without GADTs --
--------------------------

data Commands' a = Failure' | Choices' Int (Int -> NonDet' a)
  deriving Functor

type NonDet' = Free' Commands'

failure' :: NonDet' a
failure' = liftF' Failure'

instance HasEmpty NonDet' where
  emptyValue = failure'

choices' :: Int -> (Int -> NonDet' a) -> NonDet' a
choices' n = liftF' . Choices' n

nQueens' :: Int -> NonDet' Queens
nQueens' n = nQueensAcc' n n

nQueensAcc' :: Int -> Int -> NonDet' Queens
nQueensAcc' n 0 = Pure' (Queens [])
nQueensAcc' n k = nQueensAcc' n (k - 1) >>= addQueen' n

addQueen' :: Int -> Queens -> NonDet' Queens
addQueen' n = choices' n . chooseQueen' n

chooseQueen' :: Int -> Queens -> Int -> NonDet' Queens
chooseQueen' n (Queens qs) k = do guard (check qs k)
                                  return (Queens (k : qs))

runNonDetF :: Commands' a -> [a]
runNonDetF Failure'        = []
runNonDetF (Choices' n cs) = foldChoices (++) [] (runNonDet' . cs) n

runNonDet' :: NonDet' a -> [a]
runNonDet' = foldFree' runNonDetF

runQueens' :: Int -> IO ()
runQueens' = putStrLn
           . intercalate "\n\n"
           . runNonDet'
           . fmap prettyPrintQueens
           . nQueens'


instance Monad m => HasEmpty (MaybeT m) where
  emptyValue = MaybeT (return Nothing)

runInteractiveF' :: Commands' a -> MaybeT (StateT Queens IO) a
runInteractiveF' Failure' = emptyValue
runInteractiveF' (Choices' n cs) = do qs <- get
                                      liftIO $ do putStrLn "Result so far:"
                                                  putStrLn (prettyPrintQueens qs)
                                                  putStrLn $ "Choose a position between 0 and " ++ show (n - 1)
                                      k <- liftIO getLine >>= MaybeT . return . readMaybe
                                      guard (0 <= k && k < n)
                                      modify (Queens [k] <>)
                                      runInteractive' (cs k)

runInteractive' :: NonDet' a -> MaybeT (StateT Queens IO) a
runInteractive' = foldFree' runInteractiveF'


runInteractiveQueens :: Int -> IO ()
runInteractiveQueens = (printSol =<<)
                     . flip runStateT (Queens [])
                     . runMaybeT
                     . runInteractive'
                     . nQueens'

printSol :: (Maybe Queens, Queens) -> IO ()
printSol (succes, sol)= do case succes of
                            Nothing -> putStrLn "Too bad! That is not allowed. Result before crash:"
                            Just _ -> putStrLn "Congrats! Final result:"
                           putStrLn $ prettyPrintQueens sol
