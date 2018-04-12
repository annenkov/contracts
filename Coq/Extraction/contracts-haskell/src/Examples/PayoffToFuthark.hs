-- | Compiling the payoff language to Futhark

module Examples.PayoffToFuthark where

import Data.List

import ContractTranslation
import Contract
import Data.Text.Template
import qualified Data.ByteString.Lazy as S
import qualified Data.Text as T
import qualified Data.Text.Lazy as E

internalFuncName = "payoffInternal"
funcName = "payoffFun"

-- | Two lists: labels of observables and names of template variables.
-- | These lists used to translate labels and names to indices.
data Params = Params {obsP :: [String], templateP :: [String]}

fromBinOp op = case op of
                 ILAdd -> "+"
                 ILSub -> "-"
                 ILMult -> "*"
                 ILDiv -> "/"
                 ILAnd -> "&&"
                 ILOr -> "||"
                 ILLess -> "<"
                 ILLessN -> "<"
                 ILLeq -> "<="
                 ILEqual -> "=="

fromUnOp op = case op of
                ILNot -> "!"
                ILNeg -> "-"

fromTexpr params e = case e of
                Tnum n -> show n
                Tvar s -> inParens ("tenv[" ++ show (paramIndex s (templateP params)) ++ "]")

fromILTexpr params e = case e of
                  ILTplus e1 e2 -> fromILTexpr params e1 ++ " + " ++ fromILTexpr params e2
                  ILTexpr e -> fromTexpr params e

fromILTexprZ params e = case e of
                   ILTplusZ e1 e2 -> fromILTexprZ params e1 ++ " + " ++ fromILTexprZ params e2
                   ILTexprZ e -> fromILTexpr params e
                   ILTnumZ n -> show n

-- we shadow t0 variable with new bindings and this allows us to just keep the same name for updated counted everywhere
loopif cond e1 e2 t =
  let templ = template $
        T.pack
        "let t0 = (loop t0 = t0 while (!(${cond}))&&(t0 < ${t}) do t0+1) in \n if ${cond} then (${e1}) else (${e2})" in
  let ctx = [("cond", cond), ("e1",e1), ("e2", e2), ("t",t)] in
  substTempl (context $ Data.List.map (\(a1,a2) -> (T.pack a1, T.pack a2)) ctx) templ

-- | Pretty-printing Futhark code.
-- | Assumptions:
-- | the external environment is an array which is indexed with discrete time, i.e. if contact horizon is [n] then the environment should contain n values for an observable;
-- | there are only two parties in a payoff exression and payoff(p1,p2) is always traslated as positive discounted value disc[t+t0].
fromPayoff params e =
  case e of
    ILIf e' e1 e2 -> inParens ("if " ++ inParens (fromPayoff params e') ++
                                "then " ++ inParens (fromPayoff params e1) ++
                                "else " ++ inParens (fromPayoff params e2))
    ILFloat v -> show v
    ILNat n -> show n
    ILBool b -> show b
    ILtexpr e -> inParens (fromILTexpr params e) ++ " + t0"
    ILNow -> "t_now"
    ILModel (LabR (Stock l)) t ->
      -- we simplify the lookup procedure to just indexing in the environment
        inParens ("ext[" ++ (fromILTexprZ params t ++ "+ t0") ++ "," ++ show (paramIndex l (obsP params)) ++ "]")
    ILUnExpr op e -> fromUnOp op ++ " " ++ fromPayoff params e
    ILBinExpr op e1 e2 -> inParens (inParens (fromPayoff params e1) ++ spaced (fromBinOp op) ++ inParens (fromPayoff params e2))
    ILLoopIf e e1 e2 t -> loopif (fromPayoff params e)
                                 (fromPayoff params e1)
                                 (fromPayoff params e2)
                                 (fromTexpr params t)
    -- this is also a simplifying assumption:
    ILPayoff t p1' p2' -> "disc" ++ inSqBr (fromILTexpr params t ++ "+ t0")
      -- inParens (ifThenElse (show p1' ++ "== p1 && " ++ show p2' ++ "== p2") "1"
      --                                              (ifThenElse (show p1' ++ "== p2 && " ++ show p2' ++ "== p1") "-1" "0"))

-- | Two index translation functions
data IndexTrans = IndT {obsT :: Int -> Int, payoffT :: Int -> Int}

empty_tenv = (\_ -> error "Empty template env")

-- | Translation of time scale to indices.
-- | Ideally, this should be done in Coq with corresponding proofs.
-- | Reindex actually does a bit more: it evaluates template expression in the empty template environment.
-- | For that reason it works only for template-closed expressions.
reindex :: IndexTrans -> ILExpr -> ILExpr
reindex indT e =
  case e of
    ILIf e' e1 e2 -> ILIf (reindex indT e') (reindex indT e1) (reindex indT e2)
    ILFloat v -> ILFloat v
    ILNat n -> ILNat n
    ILBool b -> ILBool b
    ILtexpr e -> let n = iLTexprSem e empty_tenv in ILtexpr (ILTexpr (Tnum ((obsT indT) n)))
    ILNow -> ILNow
    ILModel (LabR (Stock l)) t -> let n = iLTexprSemZ t empty_tenv in
      ILModel (LabR (Stock l)) (ILTnumZ ((obsT indT) n))
    ILUnExpr op e -> ILUnExpr op (reindex indT e)
    ILBinExpr op e1 e2 -> ILBinExpr op (reindex indT e1) (reindex indT e2)
    ILLoopIf e e1 e2 t -> ILLoopIf (reindex indT e) (reindex indT e1)
                                   (reindex indT e2) t
    ILPayoff t p1 p2 -> let n = iLTexprSem t empty_tenv in
      ILPayoff (ILTexpr (Tnum ((payoffT indT) n))) p1 p2

reindexTexpr :: (Int -> Int) -> TExpr -> TExpr
reindexTexpr rf e = case e of
                Tnum n -> Tnum (rf n)
                Tvar s -> Tvar s

reindexILTexpr rf e = case e of
                  ILTplus e1 e2 -> ILTplus (reindexILTexpr rf e1)  (reindexILTexpr rf e2)
                  ILTexpr e -> ILTexpr (reindexTexpr rf e)

reindexILTexprZ rf e = case e of
                   ILTplusZ e1 e2 -> ILTplusZ (reindexILTexprZ rf e1) (reindexILTexprZ rf e2)
                   ILTexprZ e -> ILTexprZ (reindexILTexpr rf e)
                   ILTnumZ n -> ILTnumZ (rf n)

-- some helpers for pretty-printing
inParens s = "(" ++ s ++ ")"
inCurlBr s = "{" ++ s ++ "}"
inSqBr s = "[" ++ s ++ "]"
newLn s = "\n" ++ s
inBlock = newLn . inCurlBr . newLn
commaSeparated = intercalate ", "
surroundBy c s = c ++ s ++ c
spaced = surroundBy " "
ifThenElse cond e1 e2 = "if " ++ spaced (inParens cond) ++ "then" ++ spaced e1 ++ "else" ++ spaced e2
dec name params ty body = "let " ++ name ++ inParens params ++ ": " ++ ty ++ " = " ++ body
fcall f args = f ++ inParens (intercalate ", " args)
lambda v e = "(\\" ++ v ++ "->" ++ e ++ ")"

header = ""

payoffInternalDec params e =
  dec internalFuncName "ext : [][]f32, tenv : []i32, disc : []f32, t0 : i32, t_now : i32" "f32" (fromPayoff params e)
payoffDec = dec funcName  "ext : [][]f32, tenv : []i32, disc : []f32, t_now : i32" "f32"
                          (fcall internalFuncName  ["ext", "tenv", "disc", "0", "t_now"])
ppFutharkCode params e = payoffInternalDec params e ++ newLn payoffDec

-- | Create 'Context' from association list (taken from "template" package examples)
context :: [(T.Text, T.Text)] -> Context
context assocs x = maybe err id . lookup x $ assocs
  where err = error $ "Could not find key: " ++ T.unpack x

substTempl :: Context -> Template -> String
substTempl ctx tmpl = E.unpack $ render tmpl ctx

-- | Translate template variables according to the order they appear
-- | in the given list of variable names
paramIndex :: String -> [String] -> Int
paramIndex p =  maybe err id . findIndex (\x -> x == p)
  where err = error $ "Could not find parameter: " ++ p


wrapInModule modName code = substTempl (context ctx) modTempl
  where
    ctx = Data.List.map (\(a1,a2) -> (T.pack a1, T.pack a2))
           [("code", code),
            ("modName", modName),
            ("fcall", fcall funcName ["ext", "[]", "disc", "0"])]
    modTempl = template $ T.pack "module $modName = { $code \n\n let payoff disc _ ext = $fcall }"

compileAndWrite path params exp =
  let path' = if null path then "./" else path in
  do
    let out = header ++ ppFutharkCode params exp
    writeFile (path ++ "PayoffFunction.fut") out

