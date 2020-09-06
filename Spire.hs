{-# LANGUAGE ApplicativeDo   #-}
{-# LANGUAGE BangPatterns    #-}
{-# LANGUAGE BlockArguments  #-}
{-# LANGUAGE DeriveFunctor   #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE RecordWildCards #-}

module Main where

import Control.Applicative (empty)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Map (Map)

import qualified Control.Monad      as Monad
import qualified Data.List          as List
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map.Strict    as Map
import qualified Data.Ord           as Ord
import qualified Text.Show.Pretty   as Pretty

data Card = Strike | Defend | Ascender'sBane | Bash deriving (Eq, Ord, Show)

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
    } deriving (Eq, Ord, Show)

data Possible a = Possible { weight :: !Int, outcome :: !a }
    deriving (Functor, Show)

newtype Distribution a = Distribution { possibilities :: NonEmpty (Possible a) }
    deriving (Functor, Show)

instance Applicative Distribution where
    pure x = Distribution [ Possible 1 x ]

    (<*>) = Monad.ap

instance Monad Distribution where
    m >>= f = Distribution do
        Possible p₀ x <- possibilities m

        Possible p₁ y <- possibilities (f x)

        return $! Possible (p₀ * p₁) y

expectationValue :: Fractional n => Distribution n -> n
expectationValue distribution =
    sum (fmap tally (possibilities distribution)) / totalWeight
  where
    totalWeight = sum (fmap (fromIntegral . weight) (possibilities distribution))

    tally possible = fromIntegral (weight possible) * outcome possible

play
    :: (Fractional n, Ord n)
    => (status -> n)
    -> (status -> Bool)
    -> (status -> NonEmpty (Distribution status))
    -> status
    -> Distribution status
play objectiveFunction done choices = loop
  where
    loop status
        | done status = do
            pure status
        | otherwise = do
            let predict option = expectationValue do
                    nextStatus <- option

                    finalStatus <- loop nextStatus

                    return (objectiveFunction finalStatus)

            nextStatus <- List.maximumBy (Ord.comparing predict) (choices status)

            loop nextStatus

prune :: Ord key => Distribution key -> Distribution key
prune = mapToDistribution . distributionToMap
  where
    distributionToMap distribution = Map.fromListWith (+) do
        possible <- NonEmpty.toList (possibilities distribution)

        return (outcome possible, weight possible)

    mapToDistribution m = Distribution do
        (key, value) <- NonEmpty.fromList (Map.toList m)

        return Possible{ weight = value, outcome = key }

draw :: Status -> Distribution Status
draw status = prune do
    case select (deck status) of
        Nothing -> do
            case select (graveyard status) of
                Nothing -> do
                    error "Oops!"
                Just distribution -> do
                    (card, newDeck) <- distribution

                    return status
                        { deck = newDeck
                        , hand = increment card (hand status)
                        , graveyard = []
                        }
        Just distribution -> do
            (card, newDeck) <- distribution

            return status
                { deck = newDeck
                , hand = increment card (hand status)
                }

drawMany :: Int -> Status -> Distribution Status
drawMany 0 status = do
    return status
drawMany !n status = do
    newStatus <- draw status

    drawMany (n - 1) newStatus

handSize :: Int
handSize = 3

possibleInitialStatuses :: Distribution Status
possibleInitialStatuses = do
    status <- Distribution do
        let deck = [ (Strike, 5), (Defend, 4), (Bash, 1), (Ascender'sBane, 1) ]

        let hand = []

        let graveyard = []

        cultistHealth <- pure 56 -- [ 50 .. 56 ]

        let cultistVulnerability = 0

        let ironcladHealth = 80

        let ironcladBlock = 0

        let energy = 3

        let turn = 0

        let outcome = Status{..}

        let weight = 1

        return Possible{..}

    drawMany handSize status

select :: Ord k => Map k Int -> Maybe (Distribution (k, Map k Int))
select oldMap = do
    keyCounts <- NonEmpty.nonEmpty (Map.toList oldMap)

    return Distribution
        { possibilities = do
            (key, count) <- keyCounts

            let newMap = decrement key oldMap

            return (Possible { weight = count, outcome = (key, newMap) })
        }

decrement :: Ord k => k -> Map k Int -> Map k Int
decrement = Map.update f
  where
    f n | n <= 1    = Nothing
        | otherwise = Just (n - 1)

increment :: Ord k => k -> Map k Int -> Map k Int
increment k = Map.insertWith (+) k 1

choices :: Status -> NonEmpty (Distribution Status)
choices status = endTurn :| act
  where
    endTurn = do
        let newCultistVulnerability =
                if 1 <= cultistVulnerability status
                then cultistVulnerability status - 1
                else 0

        let cultistDamage =
                if turn status == 0 then 0 else 1 + 5 * turn status

        let cultistUnblockedDamage =
                if ironcladBlock status <= cultistDamage
                then cultistDamage - ironcladBlock status
                else 0

        let newIroncladHealth =
                if cultistUnblockedDamage <= ironcladHealth status
                then ironcladHealth status - cultistUnblockedDamage
                else 0

        let discardedHand = status
                { hand = []
                , graveyard = Map.unionWith (+) (hand status) (graveyard status)
                }

        drawnCards <- drawMany handSize discardedHand

        return drawnCards
            { cultistVulnerability = newCultistVulnerability
            , ironcladHealth = newIroncladHealth
            , ironcladBlock = 0
            , energy = 3
            , turn = turn status + 1
            }

    act = do
        (card, count) <- Map.toList (hand status)

        let cost = case card of
                Strike         -> 1
                Defend         -> 1
                Bash           -> 2
                Ascender'sBane -> 0

        let vulnerability = case card of
                Strike         -> 0
                Defend         -> 0
                Bash           -> 2
                Ascender'sBane -> 0

        let damageMultiplier = if 1 <= cultistVulnerability status then 1.5 else 1

        let baseDamage = case card of
                Strike         -> 6
                Defend         -> 0
                Bash           -> 8
                Ascender'sBane -> 0

        let damage = truncate (baseDamage * damageMultiplier)

        let block = case card of
                Strike         -> 0
                Defend         -> 5
                Bash           -> 0
                Ascender'sBane -> 0

        let newCultistHealth =
                if damage <= cultistHealth status
                then cultistHealth status - damage
                else 0

        let permitted =
                    card /= Ascender'sBane
                &&  cost <= energy status
                &&  not (card == Defend && cultistDamage <= ironcladBlock status)
              where
                cultistDamage =
                    if turn status == 0 then 0 else 1 + 5 * turn status

        let newStatus =
                status
                    { hand =
                        decrement card (hand status)
                    , graveyard =
                        increment card (graveyard status)
                    , cultistHealth =
                        newCultistHealth
                    , cultistVulnerability =
                        cultistVulnerability status + vulnerability
                    , ironcladBlock =
                        ironcladBlock status + block
                    , energy =
                        energy status - cost
                    }

        if permitted 
            then return (return newStatus)
            else empty

main :: IO ()
main = do
    Pretty.pPrint game

    Pretty.pPrint (expectationValue (fmap (fromIntegral . ironcladHealth) game))

game :: Distribution Status
game = prune do
    let objectiveFunction = fromIntegral . ironcladHealth

    let done status = ironcladHealth status <= 0 || cultistHealth status <= 0
                    || 3 <= turn status

    initialStatus <- possibleInitialStatuses

    play objectiveFunction done choices initialStatus
