{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

FoTheL state and state management, parsing of primitives, operations on
variables and macro expressions.
-}

{-# LANGUAGE FlexibleContexts #-}

{-# OPTIONS_GHC -Wall #-}

module SAD.ForTheL.Base where

import Control.Monad
import qualified Control.Monad.State.Class as MS
import Data.Char
import Data.List

import SAD.Data.Formula

import SAD.Parser.Base
import SAD.Parser.Combinators
import SAD.Parser.Primitives

import SAD.Core.SourcePos

import SAD.Data.Text.Decl (Decl(Decl))
import qualified SAD.Data.Text.Decl as Decl

import SAD.Core.Message (PIDE)
import qualified SAD.Core.Message as Message

type FTL = Parser FState

-- What do the U and the M stand for?
type UTerm   = (Formula -> Formula, Formula)
type UNotion = (Formula -> Formula, Formula, VarName)

type MTerm   = (Formula -> Formula, [Formula])
type MNotion = (Formula -> Formula, Formula, [VarName])

-- Primitive notions?
type Prim    = ([Patt], [Formula] -> Formula)

type VarName = (String, SourcePos)


data FState = FState {
  adjectiveExpr, verbExpr, notionExpr, sntExpr :: [Prim],
  cfnExpr, rfnExpr, lfnExpr, ifnExpr :: [Prim],
  cprExpr, rprExpr, lprExpr, iprExpr :: [Prim],

  tvrExpr :: [TVar], strSyms :: [[String]], varDecl :: [String],
  idCount :: Int, hiddenCount :: Int, serialCounter :: Int,
  reports :: [Message.Report], pide :: Maybe PIDE }

-- What do sn and sp (hence sntExpr and iprExpr) stand for?
-- Why is "=" introduced in both?

initFS :: Maybe PIDE -> FState
initFS = FState
  eq [] nt sn
  cf rf [] []
  [] [] [] sp
  [] [] []
  0 0 0 []
  where
    eq = [
      ([Word ["equal"], Word ["to"], Variable], zTrm (-1) "="),
      ([Word ["nonequal"], Word ["to"], Variable], Not . zTrm (-1) "=") ]
    sp = [
      ([Symbol "="], zTrm (-1) "="),
      ([Symbol "!", Symbol "="], Not . zTrm (-1) "="),
      ([Symbol "-", Symbol "<", Symbol "-"], zTrm (-2) "iLess"),
      ([Symbol "-~-"], \(m:n:_) -> zAll "" $
        Iff (zElem (zVar "") m) (zElem (zVar "") n)) ]
    sn = [ ([Symbol "=", Variable], zTrm (-1) "=") ]
    nt = [
      ([Word ["type","types"], Numeric], zType . head),
      ([Word ["typeclass","typeclasses"], Numeric], zTypeClass . head),
      ([Word ["function","functions"], Numeric], zFun . head),
      ([Word ["set","sets"], Numeric], zSet . head),
      ([Word ["element", "elements"], Numeric, Word ["of"], Variable], \(x:m:_) -> zElem x m),
      ([Word ["instance","instances"], Numeric, Word ["of"], Variable], \(x:m:_)-> zInstance x m),
      ([Word ["method","methods"], Numeric, Word ["of"], Variable], \(x:m:_)-> zMethod x m),
      ([Word ["object", "objects"], Numeric], zObj . head)]
    rf = [ ([Symbol "[", Variable, Symbol "]"], \(f:x:_) -> zApp f x)]
    cf = [
      ([Symbol "Dom", Symbol "(", Variable , Symbol ")"], zDom . head),
      ([Symbol "(", Variable, Symbol ",", Variable, Symbol ")"], \(x:y:_) -> zPair x y) ]




getExpr :: (FState -> [a]) -> (a -> FTL b) -> FTL b
getExpr e p = MS.gets e >>=  foldr ((-|-) . try . p ) mzero


getDecl :: FTL [String]
getDecl = MS.gets varDecl

addDecl :: [String] -> FTL a -> FTL a
addDecl vs p = do
  dcl <- MS.gets varDecl; MS.modify adv;
  after p $ MS.modify $ sbv dcl
  where
    adv s = s { varDecl = vs ++ varDecl s }
    sbv vs' s = s { varDecl = vs' }

getPretyped :: FTL [TVar]
getPretyped = MS.gets tvrExpr

makeDecl :: VarName -> FTL Decl
makeDecl (nm, pos) = do
  serial <- MS.gets serialCounter
  MS.modify (\st -> st {serialCounter = serial + 1})
  return $ Decl nm pos (serial + 1)

declared :: FTL MNotion -> FTL (Formula -> Formula, Formula, [Decl])
declared p = do (q, f, v) <- p; nv <- mapM makeDecl v; return (q, f, nv)

-- Predicates: verbs and adjectives
-- see the ForTheL paper, page 10
-- primVerb and primAdjective are in the ForTheL paper, TODO: understand what is 
-- primUnAdj supposed to be
primVerb, primAdjective, primUnAdj :: FTL UTerm -> FTL UTerm

primVerb      = getExpr verbExpr . primPrd
primAdjective = getExpr adjectiveExpr . primPrd
primUnAdj     = getExpr (filter (unary . fst) . adjectiveExpr) . primPrd
  where
    unary pt = Variable `notElem` pt

primPrd :: Parser st (b1 -> b1, Formula) -> ([Patt], [Formula] -> b2) 
        -> Parser st (b1 -> b1, b2)
primPrd p (pt, fm) = do
  (q, ts) <- wdPatt p pt
  return (q, fm $ zHole:ts)


-- Multi-subject predicates: [a,b are] equal
-- TODO: udnerstand what is primMultiUnAdj supposed to be

primMultiVerb, primMultiAdjective, primMultiUnAdj :: FTL UTerm -> FTL UTerm

primMultiVerb      = getExpr verbExpr . primMultiPrd
primMultiAdjective = getExpr adjectiveExpr . primMultiPrd
primMultiUnAdj     = getExpr (filter (unary . fst) . adjectiveExpr) . primMultiPrd
  where
    unary (Variable : pt) = Variable `notElem` pt
    unary (_  : pt) = unary pt
    unary _ = True

primMultiPrd :: Parser st (b1 -> b1, Formula) -> ([Patt], [Formula] -> b2)
            -> Parser st (b1 -> b1, b2)
primMultiPrd p (pt, fm) = do
  (q, ts) <- mlPatt p pt
  return (q, fm $ zHole:zSlot:ts)


-- Notions and functions

primNotion, primOfNotion :: FTL UTerm -> FTL MNotion

primNotion p  = getExpr notionExpr notion
  where
   notion (pt, fm) = do
      (q, vs, ts) <- ntPatt p pt
      return (q, fm $ zHole:ts, vs)

primOfNotion p = getExpr notionExpr notion
  where
   notion (pt, fm) = do
      (q, vs, ts) <- ofPatt p pt
      let fn v = fm $ (pVar v):zHole:ts
      return (q, foldr1 And $ map fn vs, vs)

primCmNtn :: FTL UTerm -> FTL MTerm -> FTL MNotion
primCmNtn p s = getExpr notionExpr notion
  where
   notion (pt, fm) = do
      (q, vs, as, ts) <- cmPatt p s pt
      let fn v = fm $ zHole:v:ts
      return (q, foldr1 And $ map fn as, vs)

primFun :: FTL UTerm -> FTL UTerm
primFun  = (>>= fun) . primNotion
  where
    fun (q, Trm {trName = "=", trArgs = [_, t]}, _)
      | not (occursH t) = return (q, t)
    fun _ = mzero


-- Symbolic primitives

primCpr :: Parser FState Formula -> FTL Formula
primRpr :: Parser FState Formula -> FTL (Formula -> Formula)
primLpr :: Parser FState Formula -> FTL (Formula -> Formula)
primIpr :: Parser FState Formula -> FTL (Formula -> Formula -> Formula)
primCpr = getExpr cprExpr . primCsm
primRpr = getExpr rprExpr . primRsm
primLpr = getExpr lprExpr . primLsm
primIpr = getExpr iprExpr . primIsm

primCfn :: Parser FState Formula -> FTL Formula
primRfn :: Parser FState Formula -> FTL (Formula -> Formula)
primLfn :: Parser FState Formula -> FTL (Formula -> Formula)
primIfn :: Parser FState Formula -> FTL (Formula -> Formula -> Formula)
primCfn = getExpr cfnExpr . primCsm
primRfn = getExpr rfnExpr . primRsm
primLfn = getExpr lfnExpr . primLsm
primIfn = getExpr ifnExpr . primIsm

primCsm :: Parser st a -> ([Patt], [a] -> b) -> Parser st b
primRsm :: Parser st a -> ([Patt], [a] -> t) -> Parser st (a -> t)
primLsm :: Parser st a -> ([Patt], [a] -> t) -> Parser st (a -> t)
primIsm :: Parser st a -> ([Patt], [a] -> t) -> Parser st (a -> a -> t)
primCsm p (pt, fm) = smPatt p pt >>= \l -> return $ fm l
primRsm p (pt, fm) = smPatt p pt >>= \l -> return $ \t -> fm $ t:l
primLsm p (pt, fm) = smPatt p pt >>= \l -> return $ \s -> fm $ l++[s]
primIsm p (pt, fm) = smPatt p pt >>= \l -> return $ \t s -> fm $ t:l++[s]


primSnt :: FTL Formula -> FTL MNotion
primSnt p  = noError $ varlist >>= getExpr sntExpr . snt
  where
    snt vs (pt, fm) = smPatt p pt >>= \l -> return (id, fm $ zHole:l, vs)



--See page 6 of the ForTheL paper. What the paper calls Pattern and SymbPattern are 
--implemented here as [Patt]. 

--I'm not 100% sure that Nm was supposed to be read as Numeric rather than Name,
--but neither makes a lot of sense as a constructor without arguments
--I think it is just a placeholder, like Variable, but the role of Nm is unclear by 
--looking at the ForTheL paper
data Patt = Word [String] | Symbol String | Variable | Numeric deriving (Eq, Show)


samePat :: [Patt] -> [Patt] -> Bool
samePat [] [] = True
samePat (Word ls : rst1) (Word rs : rst2) =
  all (`elem` rs) ls && samePat rst1 rst2
samePat (Variable : rst1) (Variable : rst2) = samePat rst1 rst2
samePat (Numeric : rst1) (Numeric : rst2) = samePat rst1 rst2
samePat (Symbol s : rst1) (Symbol t : rst2) = s == t && samePat rst1 rst2
samePat _ _ = False


-- adding error reporting to pattern parsing
patternWordTokenOf :: [String] -> Parser st ()
patternWordTokenOf l = label ("a word of " ++ show l) $ wdTokenOf l

patternSymbolTokenOf :: String -> Parser st ()
patternSymbolTokenOf l = label ("the symbol " ++ show l) $ smTokenOf l

-- most basic pattern parser: simply follow the pattern and parse terms with p
-- at variable places
wdPatt :: Parser st (b -> b, a) -> [Patt] -> Parser st (b -> b, [a])
wdPatt p (Word l : ls) = patternWordTokenOf l >> wdPatt p ls
wdPatt p (Variable : ls) = do
  (r, t) <- p
  (q, ts) <- wdPatt p ls
  return (r . q, t:ts)
wdPatt _ [] = return (id, [])
wdPatt _ _ = mzero

-- parses a symbolic pattern
smPatt :: Parser st a -> [Patt] -> Parser st [a]
smPatt p (Variable : ls) = liftM2 (:) p $ smPatt p ls
smPatt p (Symbol s : ls) = patternSymbolTokenOf s >> smPatt p ls
smPatt _ [] = return []
smPatt _ _ = mzero

-- parses a multi-subject pattern: follow the pattern, but ignore the wdToken
-- right before the first variable. Then check that all "and" tokens have been
-- consumed. Example pattern: [Word ["commute","commutes"], Word ["with"], Variable]. Then
-- we can parse "a commutes with c and d" as well as "a and b commute".
mlPatt :: Parser st (b -> b, a) -> [Patt] -> Parser st (b -> b, [a])
mlPatt p (Word l :_: Variable : ls) = patternWordTokenOf l >> naPatt p ls
mlPatt p (Word l : ls) = patternWordTokenOf l >> mlPatt p ls
mlPatt _ _ = mzero


-- parses a notion: follow the pattern to the name place, record names,
-- then keep following the pattern
ntPatt :: FTL (b -> b, a) -> [Patt] -> FTL (b -> b, [(String, SourcePos)], [a])
ntPatt p (Word l : ls) = patternWordTokenOf l >> ntPatt p ls
ntPatt p (Numeric : ls) = do
  vs <- namlist
  (q, ts) <- wdPatt p ls
  return (q, vs, ts)
ntPatt _ _ = mzero

-- parse an "of"-notion: follow the pattern to the notion name, then check that
-- "of" follows the name followed by a variable that is not followed by "and"
ofPatt :: FTL (b -> b, a) -> [Patt] -> FTL (b -> b, [(String, SourcePos)], [a])
ofPatt p (Word l : ls) = patternWordTokenOf l >> ofPatt p ls
ofPatt p (Numeric : Word l : Variable : ls) = do
  guard $ elem "of" l; vs <- namlist
  (q, ts) <- naPatt p ls
  return (q, vs, ts)
ofPatt _ _ = mzero

-- parse a "common"-notion: basically like the above. We use the special parser
-- s for the first variable place after the "of" since we expect multiple terms
-- here. Example: A common *divisor of m and n*.
cmPatt :: FTL (b -> b, a1)
       -> FTL (b -> c, [a2])
       -> [Patt]
       -> FTL (b -> c, [(String, SourcePos)], [a2], [a1])
cmPatt p s (Word l:ls) = patternWordTokenOf l >> cmPatt p s ls
cmPatt p s (Numeric : Word l : Variable : ls) = do
  guard $ elem "of" l; vs <- namlist; patternWordTokenOf l
  (r, as) <- s
  when (null $ tail as) $ fail "several objects expected for `common'"
  (q, ts) <- naPatt p ls
  return (r . q, vs, as, ts)
cmPatt _ _ _ = mzero

-- an auxiliary pattern parser that checks that we are not dealing wiht an "and"
-- wdToken and then continues to follow the pattern
naPatt :: Parser st (b -> b, a) -> [Patt] -> Parser st (b -> b, [a])
naPatt p (Word l : ls) = guard ("and" `notElem` l) >> patternWordTokenOf l >> wdPatt p ls
naPatt p ls = wdPatt p ls



-- Variables

namlist :: FTL [(String, SourcePos)]
namlist = varlist -|- fmap (:[]) hidden

varlist :: FTL [(String, SourcePos)]
varlist = do
  vs <- var `sepBy` wdToken ","
  nodups $ map fst vs ; return vs

nodups :: Monad f => [String] -> f ()
nodups vs = unless ((null :: [b] -> Bool) $ duplicateNames vs) $
  fail $ "duplicate names: " ++ show vs

hidden :: MS.MonadState FState m => m (String, SourcePos)
hidden = do
  n <- MS.gets hiddenCount
  MS.modify $ \st -> st {hiddenCount = succ n}
  return ('h':show n, noPos)

var :: FTL (String, SourcePos)
var = do
  pos <- getPos
  v <- satisfy (\s -> all isAlphaNum s && isAlpha (head s))
  return ('x':v, pos)

--- pretyped Variables

type TVar = ([String], Formula)

primTvr :: FTL MNotion
primTvr = getExpr tvrExpr tvr
  where
    tvr (vr, nt) = do
      vs <- varlist
      guard $ all (`elem` vr) $ map fst vs
      return (id, nt, vs)

-- free

freeVars :: Formula -> FTL [String]
freeVars f = do
  dvs <- getDecl
  return (free dvs f)

freeVarPositions :: Formula -> FTL [(String, SourcePos)]
freeVarPositions f = do
  dvs <- getDecl
  return (freePositions dvs f)

--- decl

{- produce the variables declared by a formula together with their positions. As
parameter we pass the already known variables-}
decl :: [String] -> Formula -> [VarName]
decl vs = dive
  where
    dive (All _ f) = dive f
    dive (Exi _ f) = dive f
    dive (Tag _ f) = dive f
    dive (Imp f g) = filter (noc f) (dive g)
    dive (And f g) = dive f `varNameUnion` filter (noc f) (dive g)
    dive Trm {trName = 'a':_, trArgs = v@Var{trName = u@('x':_)}:ts}
      | all (not . occurs v) ts =
          guard (u `notElem` vs) >> return (u, trPosition v)
    dive Trm{trName = "=", trArgs = [v@Var{trName = u@('x':_)}, t]}
      | isTrm t && not (occurs v t) =
          guard (u `notElem` vs) >> return (u, trPosition v)
    dive _ = []

    noc f v = not $ occurs (pVar v) f
    varNameUnion = unionBy $ \a b -> fst a == fst b

{- produce variable names declared by a formula -}
declNames :: [String] -> Formula -> [String]
declNames vs = map fst . decl vs

{- produce the bindings in a formula in a Decl data type ant take care of
the serial counter. -}
bindings :: [String] -> Formula -> FTL [Decl]
bindings vs = mapM makeDecl . decl vs


overfree :: [String] -> Formula -> Maybe String
overfree vs f
    | occurs zSlot f = Just $ "too few subjects for an m-predicate " ++ inf
    | not (null sbs) = Just $ "free undeclared variables: "   ++ sbs ++ inf
    | not (null ovl) = Just $ "overlapped variables: "        ++ ovl ++ inf
    | otherwise      = Nothing
  where
    sbs = unwords $ map showVar $ free vs f
    ovl = unwords $ map showVar $ over vs f
    inf = "\n in translation: " ++ show f

over :: [String] -> Formula -> [String]
over vs (All v f) = bvrs vs (Decl.name v) f
over vs (Exi v f) = bvrs vs (Decl.name v) f
over vs f = foldF (over vs) f

bvrs :: [String] -> String -> Formula -> [String]
bvrs vs v f
  | v `elem` vs = [v]
  | null v      = over vs f
  | otherwise   = over (v:vs) f


--- macro expressions

comma, is, art, an, the, iff, that, standFor, arrow, there, does, has, with, such :: FTL ()
comma = wdTokenOf [",", "and"]
is = wdTokenOf ["is", "be", "are"]
art = opt () $ wdTokenOf ["a","an","the"]
an = wdTokenOf ["a", "an"]
the = wdToken "the"
iff = wdToken "iff" <|> mapM_ wdToken ["if", "and", "only", "if"] -- TODO: Is the second "if" a typo?
that = wdToken "that"
standFor = wdToken "denote" <|> (wdToken "stand" >> wdToken "for")
arrow = symbol "->"
there = wdToken "there" >> wdTokenOf ["is","exist","exists"]
does = opt () $ wdTokenOf ["does", "do"]
has = wdTokenOf ["has" , "have"]
with = wdTokenOf ["with", "of", "having"]
such = wdTokenOf ["such", "so"]



--just for now:

showVar :: String -> String
showVar ('x':nm) = nm
showVar nm = nm
