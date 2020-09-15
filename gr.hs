-- http://www.cs.ox.ac.uk/people/bob.coecke/gr2.pdf
-- http://www.nearmidnight.com/domains.pdf
-- http://www.cc.kyoto-su.ac.jp/~yasugi/page/Kakenhi/escardo.pdf
-- Bicontinuous domains and some old problems in domain theory:
--   https://reader.elsevier.com/reader/sd/pii/S1571066109004757?token=10BC06EF3F750B9D1EE053BF144CFF6F640AE5AF000660D142737DB274B7EC4508CD441CE534F34F43D060E59986FE40
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MagicHash #-}
import Data.Bool
import GHC.Float
import GHC.Int
import Data.Maybe
import Data.Either
import GHC.Classes (Eq, (==), ltInt)
import GHC.Base (remInt, (+#), (-#), (*#))
import GHC.Show
import Data.List

-- | e for endpoint
class Poset a where
  (<) :: a -> a -> Maybe Bool
  (>) :: a -> a -> Maybe Bool
  a > b = case (a < b) of Just b -> Just (not b); Nothing -> Nothing

instance Poset Float where
  a < b = Just (ltFloat a b)

instance Poset Int where
  a < b = Just (ltInt a b)




newtype Div = Div Int deriving(Eq, Show)
instance Poset Div where
  (Div a) < (Div b) = 
    case (b `remInt` a == 0, a `remInt` b == 0) of
      (True, _) -> Just True
      (_, True) -> Just False
      (_, _) -> Nothing


-- | y << x <=> y approximates x
-- | y carries essential information about x
-- if we have that `x << y`, then:
--    * for ALL processes (as: N -> P) [a for approximation], union as = y
--    * there EXISTS M, for all m >= M, x <= as[m]
--  That is, after a finite number of `as`, we must compute an object that `x`
--     carries information about. 
--  Said differently, after a finite about of time,
--     the information of `x` is imbued into the information of `as`
--     (which eventually reaches `y`)
--  Put yet another way, all paths of information to y must pass through `x`.
--
class Domain a where
  (<<) :: a -> a -> Bool 

-- A total object is one that we can get to using only a sequence of
-- finite approximations. For example, a maximal element [one that cannot
--  be improved upon] is a total element.


-- directed set: for all a b in Directed, we have that there exists a u 
-- such that a <= u, b <= u and u in directed
newtype Directed a = Directed [a]

class Poset a => DCPO a where
  -- supremum of a poset: compute Least upper bound of a directed set
  supremum :: Directed a -> a

-- a DCPO can be made into a domain by stipulating that 
-- x << y iff
-- * for ALL directed sets S such that y <= supremum S
-- * there exists an s in S, such that x <= s
--
-- That is, if after an infinite process, we are able to dominate y, we can
-- dominate x in a finite process.
instance DCPO a => Domain a where


-- from the paper Bicontinuous Domains and Some Old
-- Problems in Domain Theory
class DCPO a => ContinuousDCPO a where
  -- 1. For every b in P, vv b = { a ∈ P | a << b } is directed 
  -- 2. b = lub (vvb) [lub = least upper bound]
  
  
-- class DCPO a => Bicontinuous a where
  -- has basis ]a, b[ = { x | a << x and x << b }
  -- has basis [a, b] = { x | a <= x <= b }
  


-- | cones are bicontinuous. Any point on a cone is indexed
-- by two natural numbers
data Pt = Pt Float Float

class Ring a where
  (+) :: a -> a -> a
  (-) :: a -> a -> a
  (*) :: a -> a -> a
  rone :: a
  rzero :: a

instance Ring Int where
  (I# a) + (I# b) = I# (a +# b)
  (I# a) - (I# b) = I# (a -# b)
  (I# a) * (I# b) = I# (a *# b)
  rone = 1
  rzero = 0

instance Ring Float where
  (+) = plusFloat
  (-) = minusFloat
  (*) = timesFloat
  rone = 1
  rzero = 0


instance (Ring a, Ring b) => Ring (a, b) where
   (a, b) + (a', b') = (a + a', b + b')
   (a, b) - (a', b') = (a - a', b - b')
   (a, b) * (a', b') = (a * a', b * b')
   rone = (rone, rone)
   rzero = (rzero, rzero)

-- https://en.wikipedia.org/wiki/Partially_ordered_ring
class (Poset a, Ring a) => Cone a where
 -- x <= y  implies x + z <= y + z
 -- 0 <= x, y  implies 0 <= x * y
 --
 -- this implies the usual properties:
 -- x <= y iff x - y <= 0
 -- x <= y and 0 <= z implies that (xz <= yz) 
 -- x is either in the positive set, or zero, or in the negation of the positive set.
 -- if a is non-trivial then a is infinite.


instance Poset Pt where
  (Pt a b) < (Pt a' b') = (a, a') < (b, b')


-- | Definition 3.1: Bicontinuous domains and some old problems
class Bicontinuous a where
  (<<<) :: a -> a -> Bool
  (>>>) :: a -> a -> Bool

instance Bicontinuous Pt where
  (<<<) (Pt a a') (Pt b b') = (a `ltFloat` a') && (b `ltFloat` b')
  (>>>) (Pt a a') (Pt b b') = (a `gtFloat` a') && (b `gtFloat` b')



data Interval a = Interval { il :: a, ir :: a } | IntervalJoin [Interval a]

-- a       b      a' b'
-- (-------) < (--{--}---): smaller intervals have more information
instance Poset a => Poset (Interval a) where
  (Interval a b) < (Interval a' b') = 
    let a_lt = a < a';  b_gt = b > b'
    in case (a_lt, b_gt) of
            (Just True, Just True) -> Just True 
            (Just False, Just False) -> Just False
            _ -> Nothing

class Meet a where meet :: a -> a -> Maybe a
class Join a where join :: a -> a -> Maybe a
class Poset a => LocallyFinite a where enumerate :: a -> a -> [a]

instance LocallyFinite Int where
  enumerate a b = if a < b == Just True then [a,a+1..b] else []

-- | for it to be a legal Interval, we must have that (Interval a b) < (Interval a' b')
-- | Need to generate all intervals from smaller to larger
-- (a---{a'--b'}----b)
instance LocallyFinite a => LocallyFinite (Interval a) where
  enumerate (Interval a b) (Interval a' b') = 
    case (a < a', b' < b) of
     (Just True, Just True) -> 
       let as = enumerate a a'; bs = enumerate b' b
       in  [ Interval ia ib | ia <- as, ib <- bs, ia < ib == Just True]
     _ -> []

returnI :: a -> Interval a; returnI a = Interval a a
joinI :: LocallyFinite a => Interval (Interval a) -> Interval a
joinI  (Interval iil iir) = IntervalJoin (enumerate iil iir)

--  eg: interval -> length
--
-- | (a -> Interval b) must be monotone.
bindI :: (LocallyFinite a, LocallyFinite b) => Interval a -> (a -> Interval b) -> Interval b
bindI (Interval la ra) a2b = IntervalJoin [a2b a | a <- enumerate la ra]

extract :: Interval a -> a
extract (Interval a b) = a

duplicate :: Interval a -> Interval (Interval a)
duplicate (Interval l r) = Interval (Interval l l) (Interval l r)

cobind :: Interval a -> (Interval a -> b) -> Interval b
cobind (Interval l r) ia2b = 
  Interval (ia2b (Interval l l)) (ia2b (Interval l r))


-- | concretely represent an interval. CI = concrete interval. 
-- arranged in ascending order: 
-- all [head xs <= x && x <= last xs | x <- xs] = True
data CI a = CI { unCI :: [a] } deriving(Eq, Show)

-- monotone maps are functorial for CI
fmapCI :: (a -> b) -> CI a -> CI b; fmapCI f (CI as) = CI [f a | a <- as]
returnCI :: a -> CI a; returnCI a = CI [a]
bindCI :: LocallyFinite a => (CI a) -> (a -> CI b) -> CI b
-- | take the lower set.
bindCI (CI as) a2cib = CI [head (unCI (a2cib a)) | a <- as]

joinCI :: LocallyFinite a => CI (CI a) -> CI a
joinCI (CI cis) = CI [ head(unCI ci) | ci <- cis]

extractCI :: CI a -> a
extractCI (CI as) = head as

prefixes :: [a] -> [[a]]
prefixes [] = [[]]
prefixes (a:as) = let ss = prefixes as in []:[a:s|s<-ss]

suffixes :: [a] -> [[a]]
suffixes [a] = [[a]]
suffixes as = [s ++ [last as] | s <- suffixes (init as)] ++ [[last as]]

duplicateCI (CI as) = CI [CI s | s <- (suffixes as)]

mkCI :: LocallyFinite  a => a -> a -> CI a
mkCI l r = CI (enumerate l r)

instance (Poset a, Poset b) => Poset (Either a b) where
  Left a < Left a' = a < a'
  Right b < Right b' = b < b'
  _ < _ = Nothing

instance (Poset a, Poset b) => Poset (a, b) where
  (a, b) < (a', b') = 
     case (a < a', b < b') of
        (Just True, Just True) -> Just True
        (Just False, Just False) -> Just False
        _ -> Nothing







-- ========================
-- ========================

-- | Sierpinski space. The `bottom` hides in it!
data S = T

class MeetDCPO a where
  infimum :: [a] -> a

-- class (DCPO p, MeetDCPO p) => Bicontinuous p where
  -- 1. x << y iff for all filtered sets S with an infinium sinf, we have that
  --     sinf <= x implies exists s in S, s <= y
  -- 2. upward-approx x is a filtered set with infimum x.


-- Defn 42 from domains and measurement: Globally hyperbolic => bicontinuous + compact intervals
-- Defn 37: Bicontunuous
class Poset p => GlobalHyperbolic p where
  -- x << y iff for all filtered sets, S:
  -- meet S <= x => exists s in S, s <= y

  -- for all x,  upward double arrow(x) is filtered with infimum x

  -- | compact
  search :: (Interval p) -> (p -> S) -> S


-- | Definition 16 in gr2
-- | Definition 42 in domains and measurement
-- class IntervalCls p where
--    -- | (1) each value is isomorphic to an interval
--    inject :: p -> Interval p
--    -- | (2) pre-condition: they share the same end point
--    union :: Interval p -> Interval p -> Interval p
--    enumerate :: Interval p -> [p]
--    -- | comonad
--    split :: Interval p -> p -> (Interval p, Interval p)
--    -- | it's compact so we can search
--    forall :: (p -> S) -> S
-- 
-- instance IntervalCls p => IntervalCls (Interval p) where
--   inject i = Interval i i
--   union (Interval l1 r1) (Interval l2 r2) = Interval l1 r2




