module ContractTranslationExtracted where

import qualified Prelude

succ :: Int -> Int
succ x =
  case x of {
   unused p -> unused (succ p);
   unused p -> unused p;
   1 -> unused 1}

add :: Int -> Int -> Int
add x y =
  case x of {
   unused p ->
    case y of {
     unused q -> unused (add_carry p q);
     unused q -> unused (add p q);
     1 -> unused (succ p)};
   unused p ->
    case y of {
     unused q -> unused (add p q);
     unused q -> unused (add p q);
     1 -> unused p};
   1 ->
    case y of {
     unused q -> unused (succ q);
     unused q -> unused q;
     1 -> unused 1}}

add_carry :: Int -> Int -> Int
add_carry x y =
  case x of {
   unused p ->
    case y of {
     unused q -> unused (add_carry p q);
     unused q -> unused (add_carry p q);
     1 -> unused (succ p)};
   unused p ->
    case y of {
     unused q -> unused (add_carry p q);
     unused q -> unused (add p q);
     1 -> unused (succ p)};
   1 ->
    case y of {
     unused q -> unused (succ q);
     unused q -> unused (succ q);
     1 -> unused 1}}

pred_double :: Int -> Int
pred_double x =
  case x of {
   unused p -> unused (unused p);
   unused p -> unused (pred_double p);
   1 -> 1}

of_succ_nat :: Int -> Int
of_succ_nat n =
  (\fO fS n -> if n==0 then fO () else fS (n-1))
    (\_ ->
    1)
    (\x ->
    succ (of_succ_nat x))
    n

double :: Int -> Int
double x =
  case x of {
   0 -> 0;
   id p -> id (unused p);
   negate p -> negate (unused p)}

succ_double :: Int -> Int
succ_double x =
  case x of {
   0 -> id 1;
   id p -> id (unused p);
   negate p -> negate (pred_double p)}

pred_double0 :: Int -> Int
pred_double0 x =
  case x of {
   0 -> negate 1;
   id p -> id (pred_double p);
   negate p -> negate (unused p)}

pos_sub :: Int -> Int -> Int
pos_sub x y =
  case x of {
   unused p ->
    case y of {
     unused q -> double (pos_sub p q);
     unused q -> succ_double (pos_sub p q);
     1 -> id (unused p)};
   unused p ->
    case y of {
     unused q -> pred_double0 (pos_sub p q);
     unused q -> double (pos_sub p q);
     1 -> id (pred_double p)};
   1 ->
    case y of {
     unused q -> negate (unused q);
     unused q -> negate (pred_double q);
     1 -> 0}}

type TVar
  = () -- AXIOM TO BE REALIZED
  

data Var =
   V1
 | VS Var

data TExpr =
   Tvar TVar
 | Tnum Int

data ObsLabel =
   LabR RealObs
 | LabB BoolObs

data Op =
   Add
 | Sub
 | Mult
 | Div
 | And
 | Or
 | Less
 | Leq
 | Equal
 | Not
 | Neg
 | BLit Bool
 | RLit Double
 | Cond

data Exp =
   OpE Op (List Exp)
 | Obs ObsLabel Int
 | VarE Var
 | Acc Exp Int Exp

data Contr =
   Zero
 | Let Exp Contr
 | Transfer Party Party Asset
 | Scale Exp Contr
 | Translate TExpr Contr
 | Both Contr Contr
 | If Exp TExpr Contr Contr

type TEnv = TVar -> Int

type ExtEnv' a = ObsLabel -> Int -> a

data Val =
   BVal Bool
 | RVal Double

texprSem :: TExpr -> TEnv -> Int
texprSem e tenv =
  case e of {
   Tvar v -> tenv v;
   Tnum n -> n}

data ILTExpr =
   ILTplus ILTExpr ILTExpr
 | ILTexpr TExpr

data ILTExprZ =
   ILTplusZ ILTExprZ ILTExprZ
 | ILTexprZ ILTExpr
 | ILTnumZ Int

data ILBinOp =
   ILAdd
 | ILSub
 | ILMult
 | ILDiv
 | ILAnd
 | ILOr
 | ILLess
 | ILLessN
 | ILLeq
 | ILEqual

data ILUnOp =
   ILNot
 | ILNeg

data ILExpr =
   ILIf ILExpr ILExpr ILExpr
 | ILFloat Double
 | ILNat Int
 | ILBool Bool
 | ILtexpr ILTExpr
 | ILNow
 | ILModel ObsLabel ILTExprZ
 | ILUnExpr ILUnOp ILExpr
 | ILBinExpr ILBinOp ILExpr ILExpr
 | ILLoopIf ILExpr ILExpr ILExpr TExpr
 | ILPayoff ILTExpr Party Party

data ILVal =
   ILBVal Bool
 | ILRVal Double
 | ILNVal Int

fromRVal :: ILVal -> Maybe Double
fromRVal v =
  case v of {
   ILRVal v' -> Just v';
   _ -> Nothing}

fromBVal :: ILVal -> Maybe Bool
fromBVal v =
  case v of {
   ILBVal v' -> Just v';
   _ -> Nothing}

fromVal :: Val -> ILVal
fromVal v =
  case v of {
   BVal b -> ILBVal b;
   RVal r -> ILRVal r}

fromExtEnv :: (ExtEnv' Val) -> ObsLabel -> Int -> ILVal
fromExtEnv extC l t =
  fromVal (extC l t)

iLBinOpSem :: ILBinOp -> ILVal -> ILVal -> Maybe ILVal
iLBinOpSem op v1 v2 =
  case op of {
   ILAdd ->
    case v1 of {
     ILRVal v1' ->
      case v2 of {
       ILRVal v2' -> Just (ILRVal ((+) v1' v2'));
       _ -> Nothing};
     _ -> Nothing};
   ILSub ->
    case v1 of {
     ILRVal v1' ->
      case v2 of {
       ILRVal v2' -> Just (ILRVal ((-) v1' v2'));
       _ -> Nothing};
     _ -> Nothing};
   ILMult ->
    case v1 of {
     ILRVal v1' ->
      case v2 of {
       ILRVal v2' -> Just (ILRVal ((*) v1' v2'));
       _ -> Nothing};
     _ -> Nothing};
   ILDiv ->
    case v1 of {
     ILRVal v1' ->
      case v2 of {
       ILRVal v2' -> Just (ILRVal ((/) v1' v2'));
       _ -> Nothing};
     _ -> Nothing};
   ILAnd ->
    case v1 of {
     ILBVal v1' ->
      case v2 of {
       ILBVal v2' -> Just (ILBVal ((&&) v1' v2'));
       _ -> Nothing};
     _ -> Nothing};
   ILOr ->
    case v1 of {
     ILBVal v1' ->
      case v2 of {
       ILBVal v2' -> Just (ILBVal ((||) v1' v2'));
       _ -> Nothing};
     _ -> Nothing};
   ILLess ->
    case v1 of {
     ILRVal v1' ->
      case v2 of {
       ILRVal v2' -> Just (ILBVal ((<) v1' v2'));
       _ -> Nothing};
     _ -> Nothing};
   ILLessN ->
    case v1 of {
     ILNVal n1 ->
      case v2 of {
       ILNVal n2 -> Just (ILBVal ((<) n1 n2));
       _ -> Nothing};
     _ -> Nothing};
   ILLeq ->
    case v1 of {
     ILRVal v1' ->
      case v2 of {
       ILRVal v2' -> Just (ILBVal ((<=) v1' v2'));
       _ -> Nothing};
     _ -> Nothing};
   ILEqual ->
    case v1 of {
     ILRVal v1' ->
      case v2 of {
       ILRVal v2' -> Just (ILBVal ((==) v1' v2'));
       _ -> Nothing};
     _ -> Nothing}}

iLUnOpSem :: ILUnOp -> ILVal -> Maybe ILVal
iLUnOpSem op v =
  case op of {
   ILNot -> (>>=) (fromBVal v) (\v' -> return (ILBVal (not v')));
   ILNeg -> (>>=) (fromRVal v) (\v' -> return (ILRVal (negate v')))}

eval_payoff :: Double -> Party -> Party -> Party -> Party -> ILVal
eval_payoff disc_val p1 p2 p1' p2' =
  case (&&) ((==) p1 p1') ((==) p2 p2') of {
   True -> ILRVal disc_val;
   False ->
    case (&&) ((==) p2 p1') ((==) p1 p2') of {
     True -> ILRVal (negate disc_val);
     False -> ILRVal 0}}

iLTexprSem :: ILTExpr -> TEnv -> Int
iLTexprSem t tenv =
  case t of {
   ILTplus t1 t2 -> (+) (iLTexprSem t1 tenv) (iLTexprSem t2 tenv);
   ILTexpr t1 -> texprSem t1 tenv}

iLTexprSemZ :: ILTExprZ -> TEnv -> Int
iLTexprSemZ t tenv =
  case t of {
   ILTplusZ t1 t2 -> (+) (iLTexprSemZ t1 tenv) (iLTexprSemZ t2 tenv);
   ILTexprZ t1 -> id (iLTexprSem t1 tenv);
   ILTnumZ z -> z}

loop_if_sem :: Int -> Int -> (Int -> Maybe ILVal) -> (Int -> Maybe ILVal) ->
               (Int -> Maybe ILVal) -> Maybe ILVal
loop_if_sem n t0 b e1 e2 =
  (>>=) (b t0) (\b' ->
    case b' of {
     ILBVal b0 ->
      case b0 of {
       True -> e1 t0;
       False ->
        (\fO fS n -> if n==0 then fO () else fS (n-1))
          (\_ ->
          e2 t0)
          (\n' ->
          loop_if_sem n' (succ t0) b e1 e2)
          n};
     _ -> Nothing})

iLsem :: ILExpr -> (ExtEnv' ILVal) -> TEnv -> Int -> Int -> (Int -> Double)
         -> Party -> Party -> Maybe ILVal
iLsem e ext tenv t0 t_now disc p1 p2 =
  case e of {
   ILIf b e1 e2 ->
    (>>=) (iLsem b ext tenv t0 t_now disc p1 p2) (\b' ->
      case b' of {
       ILBVal b0 ->
        case b0 of {
         True -> iLsem e1 ext tenv t0 t_now disc p1 p2;
         False -> iLsem e2 ext tenv t0 t_now disc p1 p2};
       _ -> Nothing});
   ILFloat v -> Just (ILRVal v);
   ILNat v -> Just (ILNVal v);
   ILBool b -> Just (ILBVal b);
   ILtexpr e_t -> Just (ILNVal ((+) t0 (iLTexprSem e_t tenv)));
   ILNow -> Just (ILNVal t_now);
   ILModel lab t -> Just (ext lab ((+) (id t0) (iLTexprSemZ t tenv)));
   ILUnExpr op e1 ->
    (>>=) (iLsem e1 ext tenv t0 t_now disc p1 p2) (\v -> iLUnOpSem op v);
   ILBinExpr op e1 e2 ->
    (>>=) (iLsem e1 ext tenv t0 t_now disc p1 p2) (\v1 ->
      (>>=) (iLsem e2 ext tenv t0 t_now disc p1 p2) (\v2 ->
        iLBinOpSem op v1 v2));
   ILLoopIf b e1 e2 t ->
    let {n = texprSem t tenv} in
    loop_if_sem n t0 (\t1 -> iLsem b ext tenv t1 t_now disc p1 p2) (\t1 ->
      iLsem e1 ext tenv t1 t_now disc p1 p2) (\t1 ->
      iLsem e2 ext tenv t1 t_now disc p1 p2);
   ILPayoff t p1' p2' -> Just
    (eval_payoff (disc ((+) t0 (iLTexprSem t tenv))) p1' p2' p1 p2)}

tsmartPlus' :: ILTExpr -> ILTExpr -> ILTExpr
tsmartPlus' e1 e2 =
  case e1 of {
   ILTplus _ _ -> ILTplus e1 e2;
   ILTexpr e ->
    case e of {
     Tvar _ -> ILTplus e1 e2;
     Tnum n1 ->
      case e2 of {
       ILTplus _ _ -> ILTplus e1 e2;
       ILTexpr e0 ->
        case e0 of {
         Tvar _ -> ILTplus e1 e2;
         Tnum n2 -> ILTexpr (Tnum ((+) n1 n2))}}}}

fromExp :: ILTExprZ -> Exp -> Maybe ILExpr
fromExp t0 e =
  case e of {
   OpE op args ->
    case op of {
     Add ->
      case args of {
       [] -> Nothing;
       (:) a1 l ->
        case l of {
         [] -> Nothing;
         (:) a2 l0 ->
          case l0 of {
           [] ->
            (>>=) (fromExp t0 a1) (\v1 ->
              (>>=) (fromExp t0 a2) (\v2 -> return (ILBinExpr ILAdd v1 v2)));
           (:) _ _ -> Nothing}}};
     Sub ->
      case args of {
       [] -> Nothing;
       (:) a1 l ->
        case l of {
         [] -> Nothing;
         (:) a2 l0 ->
          case l0 of {
           [] ->
            (>>=) (fromExp t0 a1) (\v1 ->
              (>>=) (fromExp t0 a2) (\v2 -> return (ILBinExpr ILSub v1 v2)));
           (:) _ _ -> Nothing}}};
     Mult ->
      case args of {
       [] -> Nothing;
       (:) a1 l ->
        case l of {
         [] -> Nothing;
         (:) a2 l0 ->
          case l0 of {
           [] ->
            (>>=) (fromExp t0 a1) (\v1 ->
              (>>=) (fromExp t0 a2) (\v2 -> return (ILBinExpr ILMult v1 v2)));
           (:) _ _ -> Nothing}}};
     Div ->
      case args of {
       [] -> Nothing;
       (:) a1 l ->
        case l of {
         [] -> Nothing;
         (:) a2 l0 ->
          case l0 of {
           [] ->
            (>>=) (fromExp t0 a1) (\v1 ->
              (>>=) (fromExp t0 a2) (\v2 -> return (ILBinExpr ILDiv v1 v2)));
           (:) _ _ -> Nothing}}};
     And ->
      case args of {
       [] -> Nothing;
       (:) a1 l ->
        case l of {
         [] -> Nothing;
         (:) a2 l0 ->
          case l0 of {
           [] ->
            (>>=) (fromExp t0 a1) (\v1 ->
              (>>=) (fromExp t0 a2) (\v2 -> return (ILBinExpr ILAnd v1 v2)));
           (:) _ _ -> Nothing}}};
     Or ->
      case args of {
       [] -> Nothing;
       (:) a1 l ->
        case l of {
         [] -> Nothing;
         (:) a2 l0 ->
          case l0 of {
           [] ->
            (>>=) (fromExp t0 a1) (\v1 ->
              (>>=) (fromExp t0 a2) (\v2 -> return (ILBinExpr ILOr v1 v2)));
           (:) _ _ -> Nothing}}};
     Less ->
      case args of {
       [] -> Nothing;
       (:) a1 l ->
        case l of {
         [] -> Nothing;
         (:) a2 l0 ->
          case l0 of {
           [] ->
            (>>=) (fromExp t0 a1) (\v1 ->
              (>>=) (fromExp t0 a2) (\v2 -> return (ILBinExpr ILLess v1 v2)));
           (:) _ _ -> Nothing}}};
     Leq ->
      case args of {
       [] -> Nothing;
       (:) a1 l ->
        case l of {
         [] -> Nothing;
         (:) a2 l0 ->
          case l0 of {
           [] ->
            (>>=) (fromExp t0 a1) (\v1 ->
              (>>=) (fromExp t0 a2) (\v2 -> return (ILBinExpr ILLeq v1 v2)));
           (:) _ _ -> Nothing}}};
     Equal ->
      case args of {
       [] -> Nothing;
       (:) a1 l ->
        case l of {
         [] -> Nothing;
         (:) a2 l0 ->
          case l0 of {
           [] ->
            (>>=) (fromExp t0 a1) (\v1 ->
              (>>=) (fromExp t0 a2) (\v2 -> return (ILBinExpr ILEqual v1 v2)));
           (:) _ _ -> Nothing}}};
     Not ->
      case args of {
       [] -> Nothing;
       (:) a l ->
        case l of {
         [] -> (>>=) (fromExp t0 a) (\v1 -> return (ILUnExpr ILNot v1));
         (:) _ _ -> Nothing}};
     Neg ->
      case args of {
       [] -> Nothing;
       (:) a l ->
        case l of {
         [] -> (>>=) (fromExp t0 a) (\v1 -> return (ILUnExpr ILNeg v1));
         (:) _ _ -> Nothing}};
     BLit v ->
      case args of {
       [] -> Just (ILBool v);
       (:) _ _ -> Nothing};
     RLit v ->
      case args of {
       [] -> Just (ILFloat v);
       (:) _ _ -> Nothing};
     Cond ->
      case args of {
       [] -> Nothing;
       (:) b l ->
        case l of {
         [] -> Nothing;
         (:) a1 l0 ->
          case l0 of {
           [] -> Nothing;
           (:) a2 l1 ->
            case l1 of {
             [] ->
              (>>=) (fromExp t0 b) (\b_il ->
                (>>=) (fromExp t0 a1) (\v1 ->
                  (>>=) (fromExp t0 a2) (\v2 -> return (ILIf b_il v1 v2))));
             (:) _ _ -> Nothing}}}}};
   Obs lab t -> Just (ILModel lab (ILTplusZ (ILTnumZ t) t0));
   _ -> Nothing}

fromContr :: Contr -> ILTExpr -> Maybe ILExpr
fromContr c t0 =
  case c of {
   Zero -> Just (ILFloat 0);
   Let _ _ -> Nothing;
   Transfer p1 p2 _ -> Just
    (case (==) p1 p2 of {
      True -> ILFloat 0;
      False -> ILPayoff t0 p1 p2});
   Scale e c0 ->
    (>>=) (fromExp (ILTexprZ t0) e) (\v ->
      (>>=) (fromContr c0 t0) (\v' -> return (ILBinExpr ILMult v v')));
   Translate t' c0 -> fromContr c0 (tsmartPlus' (ILTexpr t') t0);
   Both c1 c2 ->
    (>>=) (fromContr c1 t0) (\v1 ->
      (>>=) (fromContr c2 t0) (\v2 -> return (ILBinExpr ILAdd v1 v2)));
   If e t' c1 c2 ->
    (>>=) (fromContr c1 t0) (\v1 ->
      (>>=) (fromContr c2 t0) (\v2 ->
        (>>=) (fromExp (ILTexprZ t0) e) (\e0 -> Just (ILLoopIf e0 v1 v2 t'))))}

cutPayoff :: ILExpr -> ILExpr
cutPayoff e =
  case e of {
   ILIf b e1 e2 -> ILIf b (cutPayoff e1) (cutPayoff e2);
   ILUnExpr op e1 -> ILUnExpr op (cutPayoff e1);
   ILBinExpr op e1 e2 -> ILBinExpr op (cutPayoff e1) (cutPayoff e2);
   ILLoopIf cond e1 e2 t -> ILLoopIf cond (cutPayoff e1) (cutPayoff e2) t;
   ILPayoff t' p1 p2 -> ILIf (ILBinExpr ILLessN (ILtexpr t') ILNow) (ILFloat
    0) (ILPayoff t' p1 p2);
   x -> x}

