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
import Data.Bool
-- | e for endpoint
class Poset a where
  (<) :: a -> a -> Bool

class Poset a => JoinSemiLattice a where
  union :: a -> a -> a

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
instance DCPO a => ContinuousDCPO a where
  -- 1. For every b in P, vv b = { a ∈ P | a << b } is directed 
  -- 2. b = lub (vvb) [lub = least upper bound]
  
  
instance DCPO a => Bicontinuous a where
  -- has basis ]a, b[ = { x | a << x and x << b }
  -- has basis [a, b] = { x | a <= x <= b }
  


data Nat = Succ Nat | Nil

-- | cones are bicontinuous. Any point on a cone is indexed
-- by two natural numbers
data Cone a = Cone { coneix :: Nat -> Nat -> a }

data Interval a = Interval { il :: a, ir :: a }

-- | Sierpinski space. The `bottom` hides in it!
data S = T

class MeetDCPO a where
  infimum :: [a] -> a

class (DCPO p, MeetDCPO p) => Bincontinuous p where
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
--    split :: Interval p -> p -> (Interval p, Interval p)
--    -- | it's compact so we can search
--    forall :: (p -> S) -> S
-- 
-- instance IntervalCls p => IntervalCls (Interval p) where
--   inject i = Interval i i
--   union (Interval l1 r1) (Interval l2 r2) = Interval l1 r2
-- 




class IntervalPoset a e | a -> e  where
  -- | max(D): maximal elements of D
  pl :: a -> a -- | maximal element
  pr :: a -> a -- | maximal element
  -- Axiom 1: x = left x `cap` right x
  -- Axiom 2: if x, y in D and ir x = il y then 
  --    1. il (x cap y) = il x
  --    2. ir (x cap y) = ir y
  -- Axiom 3: each point p in upward (x) `cap` max(D) of an interval x in D
  --           determines two sub-intervals:
  --               1. il(x) `cap` p
  --               2. p `cap` ir(x)
  --          which have endpoint:
  --               ir(il(x) `cap` p) = il(x)
  --               ir(il(x) `cap` p) = p
  --
  --               il(p `cap` ir(x)) = p
  --               il(p `cap` ir(x)) = ir(x)
  --   
  
