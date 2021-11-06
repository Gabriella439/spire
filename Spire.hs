{-# LANGUAGE ApplicativeDo      #-}
{-# LANGUAGE BlockArguments     #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeOperators      #-}

{-# OPTIONS_GHC -Wall -Wno-orphans -Wno-type-defaults #-}

module Main where

import Control.Monad.State.Strict (StateT)
import Control.Monad.Trans.Class (lift)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Map (Map, (!))
import Data.MemoTrie (HasTrie(..), Reg, type (:->:))
import GHC.Generics (Generic)
import Prelude hiding (subtract)

import qualified Control.Monad              as Monad
import qualified Control.Monad.State.Strict as State
import qualified Data.MemoTrie              as MemoTrie
import qualified Data.List                  as List
import qualified Data.List.NonEmpty         as NonEmpty
import qualified Data.Map.Strict            as Map
import qualified Data.Ord                   as Ord
import qualified GHC.Generics               as Generics
import qualified Text.Show.Pretty           as Pretty

{-| A single possibility, consisting of an outcome paired with the associated
    weight of that outcome
-}
data Possibility a
    = Possibility { outcome :: !a, weight :: !Int }
    deriving (Functor, Show)

-- | A probability distribution, which is a non-empty list of weighted outcomes
newtype Distribution a
    = Distribution { possibilities :: NonEmpty (Possibility a) }
    deriving (Functor, Show)

instance Applicative Distribution where
    pure x = Distribution (pure (Possibility x 1))

    (<*>) = Monad.ap

instance Monad Distribution where
    m >>= f = Distribution do
        Possibility x weight0 <- possibilities m

        Possibility y weight1 <- possibilities (f x)

        return $! Possibility y (weight0 * weight1)

-- | Compute the expected value for a probability distribution
expectedValue :: Fractional n => Distribution n -> n
expectedValue Distribution{ possibilities } =
    totalTally / fromIntegral totalWeight
  where
    totalTally = sum (fmap tally possibilities)

    totalWeight = sum (fmap weight possibilities)

    tally Possibility{ outcome, weight } = fromIntegral weight * outcome

{-| Play the game optimally to its conclusion, always selecting the move that
    leads to the highest expected value for the given objective function
-}
play
    :: (Fractional n, Ord n, HasTrie state)
    => (state -> n)
    -- ^ Objective function, which returns the value we are trying to maximize
    -> (state -> Bool)
    -- ^ Termination function, which returns True if the game is over
    -> (state -> NonEmpty (Distribution state))
    -- ^ A function which generates the available moves from the current state
    -> state
    -- ^ The starting state
    -> Distribution state
    -- ^ The final probability distribution at the end of the game after optimal
    --   play
play objective done choices = MemoTrie.memoFix memoized
  where
    memoized loop status
        | done status = do
            pure status
        | otherwise = do
            next <- List.maximumBy (Ord.comparing predict) (choices status)

            loop next
      where
        predict choice = expectedValue do
            nextStatus <- choice

            finalStatus <- loop nextStatus

            return (objective finalStatus)

-- | Ironclad cards
data Card = Bash | Strike | Defend | Ascender'sBane
    deriving (Eq, Generic, Ord, Show)

instance HasTrie Card where
    newtype (Card :->: b) = CardTrie { unCardTrie :: Reg Card :->: b }

    trie = MemoTrie.trieGeneric CardTrie

    untrie = MemoTrie.untrieGeneric unCardTrie

    enumerate = MemoTrie.enumerateGeneric unCardTrie

-- | Game state
data Status = Status
    { cultistHealth        :: !Int
    , ironcladHealth       :: !Int
    , deck                 :: !(Map Card Int)
    , hand                 :: !(Map Card Int)
    , graveyard            :: !(Map Card Int)
    , cultistVulnerability :: !Int
    , ironcladBlock        :: !Int
    , energy               :: !Int
    , turn                 :: !Int
    } deriving (Eq, Generic, Ord, Show)

instance HasTrie Status where
    newtype (Status :->: b) = StatusTrie { unStatusTrie :: Reg Status :->: b }

    trie = MemoTrie.trieGeneric StatusTrie

    untrie = MemoTrie.untrieGeneric unStatusTrie

    enumerate = MemoTrie.enumerateGeneric unStatusTrie

instance (HasTrie k, HasTrie v, Ord k) => HasTrie (Map k v) where
    newtype (Map k v :->: b) = MapTrie { unMapTrie :: Reg [(k, v)] :->: b }

    trie f = MapTrie (trie (f . Map.fromAscList . Generics.to))

    untrie t a = untrie (unMapTrie t) (Generics.from (Map.toList a))

    enumerate t = map adapt (enumerate (unMapTrie t))
      where
        adapt (a, b) = (Map.fromAscList (Generics.to a), b)

choose :: Int -> Int -> Int
n `choose` k = factorial n `div` (factorial k * factorial (n - k))
  where
    factorial m = product [ 1 .. m ]

subsetsOf
    :: Ord k => Int -> Map k Int -> Maybe (Distribution (Map k Int, Map k Int))
subsetsOf remaining₀ pool
    | size₀ < remaining₀ = Nothing
    | otherwise = Just Distribution{ possibilities }
  where
    possibilities = loop size₀ (Map.toList pool) remaining₀ Map.empty Map.empty

    size₀ = sum (Map.elems pool)

    toPossibility subset unselected = Possibility{ weight, outcome }
      where
        weigh (key, count) = (pool ! key) `choose` count

        weight = product (map weigh (Map.toList subset))

        outcome = (subset, unselected)

    loop size keyCounts remaining selected unselected
        | size <= remaining = do
            let finalSelected =
                    Map.unionWith (+) (Map.fromList keyCounts) selected

            return (toPossibility finalSelected unselected)

        | remaining <= 0 = do
            let finalUnselected =
                    Map.unionWith (+) (Map.fromList keyCounts) unselected

            return (toPossibility selected finalUnselected)

    -- In theory we should never hit this case, but we include this to satisfy
    -- the exhaustivity checker
    loop _ [] _ selected unselected = do
        return (toPossibility selected unselected)

    loop size ((key, count) : keyCounts) remaining selected unselected = do
        let newSize = size - count

        let minN = max 0 (remaining - newSize)

        let maxN = min count remaining

        n <- NonEmpty.fromList [ minN .. maxN ]

        loop newSize keyCounts (remaining - n) (add n key selected) (add (count - n) key unselected)

-- | Draw N cards (efficiently)
drawMany :: Int -> StateT Status Distribution ()
drawMany n = do
    status <- State.get

    case subsetsOf n (deck status) of
        Nothing -> do
            -- We ran out of cards, so draw out the entire deck and shuffle
            -- in the graveyard so that we can draw the remaining cards
            let drawnCards = deck status

            State.put status
                { graveyard = Map.empty
                , hand = Map.unionWith (+) drawnCards (hand status)
                , deck = graveyard status
                }

            drawMany (n - sum (Map.elems drawnCards))

        Just distribution -> do
            (drawnCards, newDeck) <- lift distribution

            State.put status
                { deck = newDeck
                , hand = Map.unionWith (+) drawnCards (hand status)
                }

-- | All possible starting states
possibleInitialStatuses :: Distribution Status
possibleInitialStatuses = do
    status <- Distribution do
        cultistHealth <- 50 :| [ 51 .. 56 ]

        return
          Possibility
            { weight = 1
            , outcome =
                Status
                  { cultistHealth
                  , ironcladHealth = 80
                  , deck =
                      Map.fromList
                        [ (Strike, 5)
                        , (Defend, 4)
                        , (Bash, 1)
                        , (Ascender'sBane, 1)
                        ]
                  , hand = Map.empty
                  , graveyard = Map.empty
                  , cultistVulnerability = 0
                  , ironcladBlock = 0
                  , energy = 3
                  , turn = 0
                  }
            }

    State.execStateT (drawMany 5) status

subtract :: Ord k => Int -> k -> Map k Int -> Map k Int
subtract n = Map.update f
  where
    f v | v <= n    = Nothing
        | otherwise = Just (v - n)

decrement :: Ord k => k -> Map k Int -> Map k Int
decrement = subtract 1

add :: Ord k => Int -> k -> Map k Int -> Map k Int
add 0 _ = id
add n k = Map.insertWith (+) k n

increment :: Ord k => k -> Map k Int -> Map k Int
increment = add 1

subsetsByEnergy :: Int -> Map Card Int -> NonEmpty (Map Card Int, Int)
subsetsByEnergy remainingEnergy₀ hand₀ =
    loop (Map.toList hand₀) remainingEnergy₀ Map.empty
  where
    loop ((card, count) : cardCounts) remainingEnergy subset =
        case cost card of
            Just c -> do
                let maxN = min (remainingEnergy `div` c) count

                n <- 0 :| [ 1 .. maxN ]

                let energyCost = n * c

                loop cardCounts (remainingEnergy - energyCost) (add n card subset)
            _ ->
                loop cardCounts remainingEnergy subset

    loop [] remainingEnergy subset = do
        return (subset, remainingEnergy)

cost :: Card -> Maybe Int
cost card = case card of
    Strike         -> Just 1
    Defend         -> Just 1
    Bash           -> Just 2
    Ascender'sBane -> Nothing

exampleChoices :: Status -> NonEmpty (Distribution Status)
exampleChoices status₀ = do
    let heuristic subsets =
            case NonEmpty.nonEmpty filtered of
                Nothing -> subsets
                Just x  -> x
          where
            filtered = filter predicate (NonEmpty.toList subsets)
              where
                predicate (_, remainingEnergy) = remainingEnergy <= 0

    (subset, remainingEnergy) <- heuristic (subsetsByEnergy 3 (hand status₀))

    let turn = do
            State.modify (\status -> status{ energy = remainingEnergy })

            let process card count = do
                    Monad.replicateM_ count (act card)

            _ <- Map.traverseWithKey process subset

            endTurn

            beginTurn

    return (State.execStateT turn status₀)
  where
    endTurn :: StateT Status Distribution ()
    endTurn = do
        status <- State.get

        let newCultistVulnerability =
                if 1 <= cultistVulnerability status
                then cultistVulnerability status - 1
                else 0

        let cultistDamage =
                if turn status == 0
                then 0
                else 1 + 5 * turn status

        let cultistUnblockedDamage =
                if 0 < cultistHealth status && ironcladBlock status <= cultistDamage
                then cultistDamage - ironcladBlock status
                else 0

        let newIroncladHealth =
                if cultistUnblockedDamage <= ironcladHealth status
                then ironcladHealth status - cultistUnblockedDamage
                else 0

        let exhaustedHand = Map.delete Ascender'sBane (hand status)

        State.put status
            { hand = Map.empty
            , graveyard = Map.unionWith (+) exhaustedHand (graveyard status)
            , ironcladHealth = newIroncladHealth
            , cultistVulnerability = newCultistVulnerability
            }

    beginTurn :: StateT Status Distribution ()
    beginTurn = do
        drawMany 5

        State.modify (\status -> status
            { ironcladBlock = 0
            , energy = 3
            , turn = turn status + 1
            })

    act :: Card -> StateT Status Distribution ()
    act card = do
        status <- State.get

        let vulnerability = case card of
                Strike         -> 0
                Defend         -> 0
                Bash           -> 2
                Ascender'sBane -> 0

        let damageMultiplier =
                if 1 <= cultistVulnerability status then 1.5 else 1

        let baseDamage = case card of
                Strike         -> 6
                Defend         -> 0
                Bash           -> 8
                Ascender'sBane -> 0

        let damage = truncate (baseDamage * damageMultiplier :: Double)

        let block = case card of
                Strike         -> 0
                Defend         -> 5
                Bash           -> 0
                Ascender'sBane -> 0

        let newCultistHealth =
                if damage <= cultistHealth status
                then cultistHealth status - damage
                else 0

        State.put status
            { hand                 = decrement card (hand status)
            , graveyard            = increment card (graveyard status)
            , cultistHealth        = newCultistHealth
            , cultistVulnerability = cultistVulnerability status + vulnerability
            , ironcladBlock        = ironcladBlock status + block
            }

prune :: Ord status => Distribution status -> Distribution status
prune = mapToDistribution . distributionToMap
  where
    distributionToMap :: Ord status => Distribution status -> Map status Int
    distributionToMap Distribution{ possibilities } = Map.fromListWith (+) do
        Possibility{ outcome, weight } <- NonEmpty.toList possibilities

        return (outcome, weight)

    mapToDistribution :: Map status Int -> Distribution status
    mapToDistribution m = Distribution do
        (outcome, weight) <- NonEmpty.fromList (Map.toList m)

        return Possibility{ weight, outcome }

game :: Distribution Status
game = prune do
    let objective = fromIntegral . ironcladHealth

    let done status = ironcladHealth status <= 0 || cultistHealth status <= 0

    initialStatus <- possibleInitialStatuses

    play objective done exampleChoices initialStatus

main :: IO ()
main = do
    Pretty.pPrint (NonEmpty.toList (possibilities game))

    Pretty.pPrint (expectedValue (fmap (fromIntegral . ironcladHealth) game))
