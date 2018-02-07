{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
module Ref_quickcheck(tests) where
import Test.QuickCheck
import qualified Test.QuickCheck.Property as Property
import Ref_crdt
import Set(Set(Set,Coset))
import qualified Arith
import qualified Finite_Map
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Map.Strict((!?),Map)
import Data.Maybe(mapMaybe)
import Debug.Trace
import Data.List(elemIndices,(!!))

deriving instance Show Operation
instance Show Inref where
    show (D_inref (Arith.Int_of_integer n)) = "ir" ++ show n
instance Show Ref where
    show (D_ref (Arith.Int_of_integer n)) = "r" ++ show n
instance Show AntidoteKey where
    show (D_antidoteKey i) = "k" ++ show i
deriving instance Show a => Show (Set a)

deriving instance Show Operation_effector

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

instance Show Snapshot where
    show (Snapshot x) = show x

instance Show (State_ext a) where
    show s = "refs = " ++ show (state_refs s) ++ ", inrefs = " ++ show (state_inrefs s)

instance Show (Inref_state_ext a) where
    show s = "inref(" ++ show (inref_object_key s)
        ++ ", " ++ show (rev_refs s)
        ++ ", " ++ show (inUse s) ++ ")"

instance Show (Ref_state_ext a) where
    show s = "inref(" ++ show (object_key s)
        ++ ", " ++ show (dest_keys s) ++ ")"

instance (Show k, Show v) => Show (Finite_Map.Fmap k v) where
    show (Finite_Map.Fmap_of_list l) = show l

instance Show (Execution_ext a) where
    show e = "execution: \n" ++ concatMap printEvent (fmap_to_list (events e)) ++ "end\n"
        where
            printEvent (e,info) = show e
                ++ "  op       : " ++ show (event_operation info) ++ "\n"
                ++ "  pre      : " ++ show (event_state_pre info) ++ "\n"
                ++ "  post     : " ++ show (event_state_post info) ++ "\n"
                ++ "  snapshot : " ++ show (event_snapshot info) ++ "\n"
                ++ "  effectors: " ++ show (event_effectors info) ++ "\n"

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
            shrinkDep (e, z) = if Arith.integer_of_nat z <= 0 then []
                else [(e, Arith.nat_of_integer $ Arith.integer_of_nat z `div` 2),
                      (e, Arith.nat_of_integer $ Arith.integer_of_nat z - 1)]




data OprList = OprList [Opr]

instance Show OprList where
    show (OprList xs) = (concatMap (\(i,o) -> "  e" ++ show i ++ "  " ++ show o ++ "\n") (zip [0..] xs)) ++ "\n----end--"

removeDuplicates [] = []
removeDuplicates ((k,v):rest) = (k,v) : removeDuplicates (filter (\(k',v') -> k' /= k) rest)

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
    return $ Opr o (removeDuplicates [(a,an),(b,bn)])

gen_oprlist :: Int -> Gen [Opr]
gen_oprlist 0 = return $ []
gen_oprlist n = do
    start <- gen_oprlist (n-1)
    opr <- gen_opr (length start)
    return (opr:start)

event_num (D_event i) = fromInteger $ Arith.integer_of_int i

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
                            Just $ Opr o (removeDuplicates (concatMap renameDep deps))
                        else
                            Nothing
                    renameDep (e,i) = case m !? event_to_int e of
                        Nothing ->
                            let Opr o2 deps2 = xs !! event_num e in
                                (concatMap renameDep deps2)
                        Just a -> [(int_to_event a, i)]

make_transactional l = map (\(e,i) -> (e,100)) l

transactional = False

from_opr (Opr o l) =
    let l' = if transactional then make_transactional l else l in
    (o, Finite_Map.Fmap_of_list l')

from_opr_list (OprList ops) = (map from_opr ops)

result :: String -> [Bool] -> Property.Result
result message prop = Property.MkResult
    {   Property.ok            = Just (and prop)
      , Property.expect        = True
      , Property.reason        = "failed property " ++ show (elemIndices False prop) ++ "\n" ++ message
      , Property.theException  = Nothing
      , Property.abort         = True
      , Property.maybeNumTests = Nothing
      , Property.labels        = Map.empty
      , Property.stamp         = Set.empty
      , Property.callbacks     = []
      , Property.testCase      = []
      }

tests = quickCheckWith stdArgs { maxSuccess = 50000 } $
  (\ops ->
    let ops2 = take 20 (from_opr_list ops) in
    let exec = execution_run2 ops2 in
    result ("execution = " ++ show exec) [
        invariant1 exec,
        invariant2 exec,
        invariant3 exec,
        invariant4 exec
    ])
