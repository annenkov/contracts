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
funcName = "payoff"

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
                Tvar s -> inParens ("tenv[" ++ show (paramIndex s params) ++ "]")

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
-- | payoff expression contains only one observable;
-- | there are only two parties in a payoff exression and payoff(p1,p2) is always traslated as positive discounted value disc[t+t0].
fromPayoff params e = case e of
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
                     inParens ("ext[" ++ (fromILTexprZ params t ++ "+ t0") ++ "]")
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
  dec internalFuncName "ext : []f64, tenv : []i32, disc : []f64, t0 : i32, t_now : i32" "f64" (fromPayoff params e)
payoffDec = dec funcName  "ext : []f64, tenv : []i32, disc : []f64, t_now : i32" "f64"
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

compileAndWrite path params exp =
  let path' = if null path then "./" else path in
  do
    let out = header ++ ppFutharkCode params exp
    writeFile (path ++ "PayoffFunction.fut") out

