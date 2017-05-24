module Main where

-- An abstract interpreter implemented based on the following blog post by
-- Matt Might:
--     http://matt.might.net/articles/intro-static-analysis/

import Data.List (intersperse)
import qualified Data.Map as M
import qualified Data.Set as S

--------------------------------------------------------------------------------
--                               DATA TYPES
--------------------------------------------------------------------------------

type Name = String

data Cmd
    = Label Name
    | Goto Name
    | Assign Name Exp
    | If Exp Name
    deriving (Show, Eq, Ord)

data Exp
    = Num Int
    | Plus Exp Exp
    | Mult Exp Exp
    | Var Name
    deriving (Show, Eq, Ord)

-- A simple example
ex1 :: [Cmd]
ex1 =
    [ Assign "x" (Num 10)
    , Assign "n" (Num 1)
    , Label "loop"
    , Assign "x" (Plus (Var "x") (Num (-1)))
    , Assign "n" (Plus (Var "n") (Var "n"))
    , If (Var "x") "loop"
    , Label "end"
    ]

--------------------------------------------------------------------------------
--                           CONCRETE INTERPRETATION
--------------------------------------------------------------------------------

type Env = M.Map Name Int

-- A state stores an index into the command list (the current instruction) and
-- an environment, which tells us the current values of our variables.
type State = (Int, Env)

step :: [Cmd] -> State -> State
step cmds (idx, env)
    | idx >= length cmds || idx < 0 = error "out of bounds"
    | otherwise                     = case cmds !! idx of
        Label _    -> (idx + 1, env)
        Goto n     -> (jump n cmds, env)
        Assign n e -> (idx + 1, M.insert n (eval env e) env)
        If e n     -> let cond = eval env e in
            if cond == 0 then (idx + 1, env)
            else (jump n cmds, env)

run :: [Cmd] -> Env
run = run' 0 M.empty
    where
    run' :: Int -> Env -> [Cmd] -> Env
    run' idx env cmds = case step cmds (idx, env) of
        (idx', env') | idx' == length cmds -> env'
        (idx', env')                       -> run' idx' env' cmds

jump :: Name -> [Cmd] -> Int
jump = jump' 0
    where
    jump' :: Int -> Name -> [Cmd] -> Int
    jump' i n []                      = error "jump to nonexistent label"
    jump' i n (Label n':cs) | n == n' = i
    jump' i n (_       :cs)           = jump' (i + 1) n cs

eval :: Env -> Exp -> Int
eval env (Num n   ) = n
eval env (Plus e f) = eval env e + eval env f
eval env (Mult e f) = eval env e * eval env f
eval env (Var x   ) = env M.! x

--------------------------------------------------------------------------------
--                           ABSTRACT INTERPRETATION
--------------------------------------------------------------------------------

data AInt = Pos | Zero | Neg deriving (Show, Eq, Ord)

type AEnv = M.Map Name (S.Set AInt)

type AState = (Int, AEnv)

α :: Int -> AInt
α 0         = Zero
α n | n > 0 = Pos
α _         = Neg

aStep :: [Cmd] -> AState -> S.Set AState
aStep cmds (idx, env)
    | idx >  length cmds || idx < 0 = error "out of bounds"
    | idx == length cmds            = S.empty
    | otherwise                     = case cmds !! idx of
        Label _    -> S.singleton (idx + 1, env)
        Goto n     -> S.singleton (jump n cmds, env)
        Assign n e -> S.singleton (idx + 1, M.insert n (aEval env e) env)
        If e n     -> let eRes = aEval env e in S.fromList $ []
            ++ (if eRes == S.singleton Zero then [ ((idx + 1)  , env) ] else [])
            ++ (if S.notMember Zero eRes    then [ (jump n cmds, env) ] else [])

aPlus :: AInt -> AInt -> S.Set AInt
aPlus Zero a    = S.singleton a
aPlus a    Zero = S.singleton a
aPlus Pos  Pos  = S.singleton Pos
aPlus Neg  Neg  = S.singleton Neg
aPlus Pos  Neg  = S.fromList [Pos, Zero, Neg]
aPlus Neg  Pos  = S.fromList [Pos, Zero, Neg]

aPlusS :: S.Set AInt -> S.Set AInt -> S.Set AInt
aPlusS s1 s2 = S.unions [aPlus e1 e2 | e1 <- S.toList s1, e2 <- S.toList s2]

aMult :: AInt -> AInt -> S.Set AInt
aMult Zero a    = S.singleton Zero
aMult a    Zero = S.singleton Zero
aMult Pos  Pos  = S.singleton Pos
aMult Neg  Neg  = S.singleton Pos
aMult Pos  Neg  = S.singleton Neg
aMult Neg  Pos  = S.singleton Neg

aMultS :: S.Set AInt -> S.Set AInt -> S.Set AInt
aMultS s1 s2 = S.unions [aMult e1 e2 | e1 <- S.toList s1, e2 <- S.toList s2]

aEval :: AEnv -> Exp -> S.Set AInt
aEval env (Num n   ) = S.singleton (α n)
aEval env (Plus e f) = aPlusS (aEval env e) (aEval env f)
aEval env (Mult e f) = aMultS (aEval env e) (aEval env f)
aEval env (Var x   ) = env M.! x

analyze :: [Cmd] -> S.Set AState -> S.Set AState -> S.Set AState
analyze cmds todo seen =
    if null todo then
        seen
    else
        let (cur, rest) = S.deleteFindMin todo
            curKids = aStep cmds cur
        in
        analyze
            cmds
            (S.union rest (S.filter (\st -> S.notMember st seen) curKids))
            (S.insert cur seen)

--------------------------------------------------------------------------------
--                               EXPERIMENTS
--------------------------------------------------------------------------------

-- Pretty-printer for analysis output
showAnalysis :: S.Set AState -> String
showAnalysis states = concat $ intersperse "\n" $ map show $ S.toList states

-- Main function runs analysis and prints output
main :: IO ()
main = do
    putStrLn $ showAnalysis $ analyze ex1 (S.singleton (0, M.empty)) S.empty
    return ()
