{-# LANGUAGE ApplicativeDo              #-}
{-# LANGUAGE BlockArguments             #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE ExplicitNamespaces         #-}
{-# LANGUAGE NamedFieldPuns             #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

{-# OPTIONS_GHC -Wall -Wno-orphans -Wno-type-defaults #-}

module Main where

import Control.Monad.State.Strict (StateT)
import Control.Monad.Trans.Class (lift)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Map (Map, (!))
import Data.MemoTrie (HasTrie(..), Reg, type (:->:))
import GHC.Generics (Generic)
import GHC.Exts (IsList)

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
    deriving stock (Functor)
    deriving newtype (IsList)

instance Show a => Show (Distribution a) where
    show distribution = show (NonEmpty.toList (possibilities distribution))

instance Applicative Distribution where
    pure x = Distribution (pure (Possibility x 1))

    (<*>) = Monad.ap

instance Monad Distribution where
    m >>= f = Distribution do
        Possibility x weight0 <- possibilities m

        Possibility y weight1 <- possibilities (f x)

        return $! Possibility y (weight0 * weight1)

-- | Compute the expected value for a probability distribution
expectedValue :: Fractional number => Distribution number -> number
expectedValue Distribution{ possibilities } =
    totalTally / fromIntegral totalWeight
  where
    totalTally = sum (fmap tally possibilities)

    totalWeight = sum (fmap weight possibilities)

    tally Possibility{ outcome, weight } = fromIntegral weight * outcome

-- | Play the game optimally to its conclusion
play
    :: (Fractional number, Ord number, HasTrie state)
    => (state -> number)
    -- ^ Objective function
    -> (state -> [Distribution state])
    -- ^ A function which generates the available moves
    -> state
    -- ^ The starting state
    -> Distribution state
    -- ^ The final probability distribution
play objectiveFunction toChoices = MemoTrie.memoFix memoized
  where
    memoized loop status
        | null choices = do
            pure status

        | otherwise = do
            next <- List.maximumBy (Ord.comparing predict) choices

            loop next
      where
        choices = toChoices status

        predict choice = expectedValue do
            nextStatus <- choice

            finalStatus <- loop nextStatus

            return (objectiveFunction finalStatus)

-- | Play the game optimally for one step
step
    :: (Fractional number, Ord number, HasTrie state)
    => (state -> number)
    -- ^ Objective function
    -> (state -> [Distribution state])
    -- ^ A function which generates the available moves
    -> state
    -- ^ The starting state
    -> Maybe (Distribution state)
    -- ^ The final probability distribution
step objectiveFunction toChoices status =
    case choices of
        []         -> Nothing
        [ choice ] -> Just choice
        _          -> Just (List.maximumBy (Ord.comparing predict) choices)
  where
    choices = toChoices status

    predict choice = expectedValue do
        nextStatus <- choice

        finalStatus <- play objectiveFunction toChoices nextStatus

        return (objectiveFunction finalStatus)

-- | Prune a `Distribution` by consolidating duplicate outcomes
prune :: Ord status => Distribution status -> Distribution status
prune = mapToDistribution . distributionToMap
  where
    distributionToMap :: Ord status => Distribution status -> Map status Int
    distributionToMap Distribution{ possibilities } = Map.fromListWith (+) do
        ~Possibility{ outcome, weight } <- NonEmpty.toList possibilities

        return (outcome, weight)

    mapToDistribution :: Map status Int -> Distribution status
    mapToDistribution m = Distribution do
        ~(outcome, weight) <- NonEmpty.fromList (Map.toList m)

        return Possibility{ weight, outcome }

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

        loop newSize keyCounts (remaining - n) (increase n key selected) (increase (count - n) key unselected)

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

decrease :: Ord k => Int -> k -> Map k Int -> Map k Int
decrease 0 _ = id
decrease n k = Map.update f k
  where
    f v | v <= n    = Nothing
        | otherwise = Just (v - n)

increase :: Ord k => Int -> k -> Map k Int -> Map k Int
increase 0 _ = id
increase n k = Map.insertWith (+) k n

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

                loop cardCounts (remainingEnergy - energyCost) (increase n card subset)
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

exampleChoices :: Status -> [Distribution Status]
exampleChoices status₀ = do
    let done = ironcladHealth status₀ <= 0 || cultistHealth status₀ <= 0

    Monad.guard (not done)

    let heuristic subsets
            | null filtered = subsets
            | otherwise     = filtered
          where
            filtered = filter predicate subsets
              where
                predicate (_, remainingEnergy) = remainingEnergy <= 0

    ~(subset, remainingEnergy) <- heuristic (NonEmpty.toList (subsetsByEnergy 3 (hand status₀)))

    return do
        let turn = do
                State.modify (\status -> status{ energy = remainingEnergy })

                let process card count = do
                        Monad.replicateM_ count (act card)

                _ <- Map.traverseWithKey process subset

                endTurn

                beginTurn

        State.execStateT turn status₀
  where
    endTurn :: StateT Status Distribution ()
    endTurn = do
        status <- State.get

        let newCultistVulnerability = max 0 (cultistVulnerability status - 1)

        let cultistDamage = if turn status == 0 then 0 else 1 + 5 * turn status

        let cultistUnblockedDamage =
                if 0 < cultistHealth status
                then max 0 (cultistDamage - ironcladBlock status)
                else 0

        let newIroncladHealth =
                max 0 (ironcladHealth status - cultistUnblockedDamage)

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
                Bash -> 2
                _    -> 0

        let damageMultiplier =
                if 1 <= cultistVulnerability status then 1.5 else 1

        let baseDamage = case card of
                Strike -> 6
                Bash   -> 8
                _      -> 0

        let damage = truncate (baseDamage * damageMultiplier :: Double)

        let block = case card of
                Defend -> 5
                _      -> 0

        let newCultistHealth = max 0 (cultistHealth status - damage)

        State.put status
            { hand                 = decrease 1 card (hand status)
            , graveyard            = increase 1 card (graveyard status)
            , cultistHealth        = newCultistHealth
            , cultistVulnerability = cultistVulnerability status + vulnerability
            , ironcladBlock        = ironcladBlock status + block
            }

objective :: Status -> Double
objective = fromIntegral . ironcladHealth

game :: Distribution Status
game = prune do
    initialStatus <- pure turn₁ -- possibleInitialStatuses

    play objective exampleChoices initialStatus

turn₁ :: Status
turn₁ = Status
    { cultistHealth = 53
    , ironcladHealth = 68
    , deck =
        Map.fromList
            [ (Strike, 2), (Defend, 2), (Bash, 1), (Ascender'sBane, 1) ]
    , hand = Map.fromList [ (Strike, 3), (Defend, 2)  ]
    , graveyard = Map.empty
    , cultistVulnerability = 0
    , ironcladBlock = 0
    , energy = 3
    , turn = 0
    }

turn₂ :: Status
turn₂ = Status
    { cultistHealth = 35
    , ironcladHealth = 68
    , deck = Map.fromList [ (Defend, 1) ]
    , hand =
        Map.fromList
            [ (Bash, 1), (Strike, 2), (Defend, 1), (Ascender'sBane, 1) ]
    , graveyard = Map.fromList [ (Strike, 3) , (Defend, 2) ]
    , cultistVulnerability = 0
    , ironcladBlock = 0
    , energy = 3
    , turn = 1
    }

turn₃ :: Status
turn₃ = Status
    { cultistHealth = 27
    , ironcladHealth = 67
    , deck = Map.fromList [ (Strike, 3), (Defend, 2) ]
    , hand = Map.fromList [ (Bash, 1), (Strike, 2), (Defend, 2) ]
    , graveyard = Map.fromList []
    , cultistVulnerability = 1
    , ironcladBlock = 0
    , energy = 3
    , turn = 2
    }

turn₄ :: Status
turn₄ = Status
    { cultistHealth = 18
    , ironcladHealth = 66
    , deck = Map.fromList []
    , hand = Map.fromList [ (Strike, 3), (Defend, 2) ]
    , graveyard = Map.fromList [ (Bash, 1), (Strike, 2) , (Defend, 2) ]
    , cultistVulnerability = 0
    , ironcladBlock = 0
    , energy = 3
    , turn = 3
    }

main :: IO ()
main = do
    Pretty.pPrint (NonEmpty.toList (possibilities game))

    Pretty.pPrint (expectedValue (fmap (fromIntegral . ironcladHealth) game))

    Pretty.pPrint (step objective exampleChoices turn₂)
