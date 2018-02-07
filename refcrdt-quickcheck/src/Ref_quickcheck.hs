{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
module Ref_quickcheck(tests) where
import Test.QuickCheck
import Ref_crdt
import Set(Set(Set,Coset))
import qualified Arith
import qualified Finite_Map
import qualified Data.Map.Strict as Map
import Data.Map.Strict((!?),Map)
import Data.Maybe(mapMaybe)
import Debug.Trace

deriving instance Show Operation
instance Show Inref where
    show (D_inref (Arith.Int_of_integer n)) = "ir" ++ show n
instance Show Ref where
    show (D_ref (Arith.Int_of_integer n)) = "r" ++ show n
deriving instance Show AntidoteKey
deriving instance Show a => Show (Set a)

instance Show Arith.Nat where
    show x = show $ Arith.integer_of_nat x
instance Arbitrary Arith.Nat where
    arbitrary = do
        x <- arbitrary
        return $ Arith.nat_of_integer x

instance Show Arith.Int where
    show x = show $ Arith.integer_of_int x
deriving instance Arbitrary Arith.Int;

event_to_int :: Event -> Int
event_to_int (D_event n) = fromIntegral $ Arith.integer_of_int n

int_to_event :: Int -> Event
int_to_event n = D_event $ Arith.Int_of_integer $ toInteger n

instance Show Event where
    show (D_event n) = "e" ++ show n

instance Num Arith.Nat where
    m + n = Arith.nat_of_integer (Arith.integer_of_nat m + Arith.integer_of_nat n)
    m * n = Arith.nat_of_integer (Arith.integer_of_nat m * Arith.integer_of_nat n)
    abs m = m
    signum m = 1
    negate m = Arith.nat_of_integer 0
    fromInteger n = Arith.nat_of_integer n

instance Num Arith.Int where
    m + n = Arith.Int_of_integer (Arith.integer_of_int m + Arith.integer_of_int n)
    m * n = Arith.Int_of_integer (Arith.integer_of_int m * Arith.integer_of_int n)
    abs m = m
    signum m = 1
    negate m = Arith.Int_of_integer (- Arith.integer_of_int m)
    fromInteger n = Arith.Int_of_integer n


instance Arbitrary a => Arbitrary (Set a) where
    arbitrary = do
        x <- arbitrary
        return $ Set x

instance Arbitrary Inref where
    arbitrary = do
        x <- oneof (map return [1,2])
        return $ D_inref (Arith.Int_of_integer x)
instance Arbitrary Ref where
    arbitrary = do
        x <- oneof (map return [1,2,3])
        return $ D_ref (Arith.Int_of_integer x)

instance Arbitrary Operation where
    arbitrary = oneof [
        do
            x <- arbitrary
            y <- arbitrary
            return $ Init x y,
        do
            x <- arbitrary
            y <- arbitrary
            return $ Assign x y,
        do
            x <- arbitrary
            return $ Reset_ref x,
        do
            x <- arbitrary
            return $ May_delete x []]

-- instance Arbitrary Operation where
--     arbitrary = oneof [
--         do
--             x <- arbitrary
--             y <- arbitrary
--             return $ Init x y,
--         do
--             x <- arbitrary
--             y <- arbitrary
--             return $ Assign x y,
--         do
--             x <- arbitrary
--             return $ Deref x,
--         do
--             x <- arbitrary
--             return $ May_delete x [],
--         do
--             x <- arbitrary
--             return $ Reset_inref x,
--         do
--             x <- arbitrary
--             return $ Reset_ref x]

-- instance Show Operation where
-- 	Init Ref Inref
-- 	Assign Ref Ref
-- 	Deref Ref
--     May_delete Inref [Ref]
--     Reset_inref Inref
--     Reset_ref Ref

data Opr = Opr Operation [(Event, Arith.Nat)]

instance Show Opr where
    show (Opr opr l) = show opr ++ " " ++ show l

instance Arbitrary Opr where
    arbitrary = do
        o <- arbitrary
        a <- oneof (map (return . D_event) [1,2,3,4,5])
        an' <- arbitrary
        let an = Arith.nat_of_integer (an' `mod` 2)
        b <- oneof (map (return . D_event) [1,2,3,4,5,8,9,10])
        bn' <- arbitrary
        let bn = Arith.nat_of_integer (bn' `mod` 3)
        return $ Opr o [(a,an),(b,bn)]

    shrink (Opr o xs) = map (Opr o) (shrinkList shrinkDep xs)
        where
            shrinkDep (e, z) = [(e, Arith.nat_of_integer $ Arith.integer_of_nat z `div` 2),
                                (e, Arith.nat_of_integer $ Arith.integer_of_nat z - 1)]




data OprList = OprList [Opr]

instance Show OprList where
    show (OprList xs) = (concatMap (\(i,o) -> "  e" ++ show i ++ "  " ++ show o ++ "\n") (zip [0..] xs)) ++ "\n----end--"


gen_opr :: Int -> Gen Opr
gen_opr 0 = do
    o <- arbitrary
    return $ Opr o []
gen_opr n = do
    o <- arbitrary
    a' <- arbitrary
    let a = D_event $ Arith.Int_of_integer $ (a' `mod` toInteger n)
    an' <- arbitrary
    let an = Arith.nat_of_integer (an' `mod` 2)
    b' <- arbitrary
    let b = D_event $ Arith.Int_of_integer $ (b' `mod` toInteger n)
    bn' <- arbitrary
    let bn = Arith.nat_of_integer (bn' `mod` 3)
    return $ Opr o [(a,an),(b,bn)]

gen_oprlist :: Int -> Gen [Opr]
gen_oprlist 0 = return $ []
gen_oprlist n = do
    start <- gen_oprlist (n-1)
    opr <- gen_opr (length start)
    return (opr:start)



instance Arbitrary OprList where

    arbitrary = do
        l <- sized gen_oprlist
        return $ OprList (reverse l)

    shrink (OprList xs) =
        map OprList $ map filtered newIntsList
        where
            newIntsList :: [[Int]]
            newIntsList = shrinkList shrinkNothing [0..length xs-1]

            filtered :: [Int] -> [Opr]
            filtered newInts = mapMaybe filterOp (zip [0..] xs)
                where
                    m :: Map Int Int
                    m = Map.fromList (zip newInts [0..])
                    filterOp (e, Opr o deps) =
                        if Map.member e m then
                            Just $ Opr o (mapMaybe renameDep deps)
                        else
                            Nothing
                    renameDep (e,i) = case m !? event_to_int e of
                        Nothing -> Nothing
                        Just a -> Just (int_to_event a, i)

make_transactional l = map (\(e,i) -> (e,100)) l

transactional = False

from_opr (Opr o l) =
    let l' = if transactional then make_transactional l else l in
    (o, Finite_Map.Fmap_of_list l')

from_opr_list (OprList ops) = (map from_opr ops)

tests = quickCheckWith stdArgs { maxSuccess = 500000 } $
  (\ops ->
    let ops2 = take 20 (from_opr_list ops) in
    invariant2 (execution_run2 ops2))
