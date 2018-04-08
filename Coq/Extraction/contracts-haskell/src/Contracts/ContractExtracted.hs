module ContractExtracted where

import qualified Prelude

compOpp :: Ordering -> Ordering
compOpp r =
  case r of {
   EQ -> EQ;
   LT -> GT;
   GT -> LT}

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

compare_cont :: Ordering -> Int -> Int -> Ordering
compare_cont r x y =
  case x of {
   unused p ->
    case y of {
     unused q -> compare_cont r p q;
     unused q -> compare_cont GT p q;
     1 -> GT};
   unused p ->
    case y of {
     unused q -> compare_cont LT p q;
     unused q -> compare_cont r p q;
     1 -> GT};
   1 ->
    case y of {
     1 -> r;
     _ -> LT}}

compare :: Int -> Int -> Ordering
compare =
  compare_cont EQ

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

compare0 :: Int -> Int -> Ordering
compare0 x y =
  case x of {
   0 ->
    case y of {
     0 -> EQ;
     id _ -> LT;
     negate _ -> GT};
   id x' ->
    case y of {
     id y' -> compare x' y';
     _ -> GT};
   negate x' ->
    case y of {
     negate y' -> compOpp (compare x' y');
     _ -> LT}}

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

data Ty =
   REAL
 | BOOL

type TEnv = TVar -> Int

type ExtEnv' a = ObsLabel -> Int -> a

adv_ext :: Int -> (ExtEnv' a1) -> ExtEnv' a1
adv_ext d e l x =
  e l ((+) d x)

type Env' a = List a

lookupEnv :: Var -> (Env' a1) -> Maybe a1
lookupEnv v env =
  case v of {
   V1 ->
    case env of {
     [] -> Nothing;
     (:) x _ -> Just x};
   VS v0 ->
    case env of {
     [] -> Nothing;
     (:) _ xs -> lookupEnv v0 xs}}

data Val =
   BVal Bool
 | RVal Double

acc_sem :: (Int -> a1 -> a1) -> Int -> a1 -> a1
acc_sem f n z =
  (\fO fS n -> if n==0 then fO () else fS (n-1))
    (\_ ->
    z)
    (\n' ->
    f n (acc_sem f n' z))
    n

opSem :: Op -> (List Val) -> Maybe Val
opSem op vs =
  case op of {
   Add ->
    case vs of {
     [] -> Nothing;
     (:) v l ->
      case v of {
       BVal _ -> Nothing;
       RVal x ->
        case l of {
         [] -> Nothing;
         (:) v0 l0 ->
          case v0 of {
           BVal _ -> Nothing;
           RVal y ->
            case l0 of {
             [] -> Just (RVal ((+) x y));
             (:) _ _ -> Nothing}}}}};
   Sub ->
    case vs of {
     [] -> Nothing;
     (:) v l ->
      case v of {
       BVal _ -> Nothing;
       RVal x ->
        case l of {
         [] -> Nothing;
         (:) v0 l0 ->
          case v0 of {
           BVal _ -> Nothing;
           RVal y ->
            case l0 of {
             [] -> Just (RVal ((-) x y));
             (:) _ _ -> Nothing}}}}};
   Mult ->
    case vs of {
     [] -> Nothing;
     (:) v l ->
      case v of {
       BVal _ -> Nothing;
       RVal x ->
        case l of {
         [] -> Nothing;
         (:) v0 l0 ->
          case v0 of {
           BVal _ -> Nothing;
           RVal y ->
            case l0 of {
             [] -> Just (RVal ((*) x y));
             (:) _ _ -> Nothing}}}}};
   Div ->
    case vs of {
     [] -> Nothing;
     (:) v l ->
      case v of {
       BVal _ -> Nothing;
       RVal x ->
        case l of {
         [] -> Nothing;
         (:) v0 l0 ->
          case v0 of {
           BVal _ -> Nothing;
           RVal y ->
            case l0 of {
             [] -> Just (RVal ((/) x y));
             (:) _ _ -> Nothing}}}}};
   And ->
    case vs of {
     [] -> Nothing;
     (:) v l ->
      case v of {
       BVal x ->
        case l of {
         [] -> Nothing;
         (:) v0 l0 ->
          case v0 of {
           BVal y ->
            case l0 of {
             [] -> Just (BVal ((&&) x y));
             (:) _ _ -> Nothing};
           RVal _ -> Nothing}};
       RVal _ -> Nothing}};
   Or ->
    case vs of {
     [] -> Nothing;
     (:) v l ->
      case v of {
       BVal x ->
        case l of {
         [] -> Nothing;
         (:) v0 l0 ->
          case v0 of {
           BVal y ->
            case l0 of {
             [] -> Just (BVal ((||) x y));
             (:) _ _ -> Nothing};
           RVal _ -> Nothing}};
       RVal _ -> Nothing}};
   Less ->
    case vs of {
     [] -> Nothing;
     (:) v l ->
      case v of {
       BVal _ -> Nothing;
       RVal x ->
        case l of {
         [] -> Nothing;
         (:) v0 l0 ->
          case v0 of {
           BVal _ -> Nothing;
           RVal y ->
            case l0 of {
             [] -> Just (BVal ((<) x y));
             (:) _ _ -> Nothing}}}}};
   Leq ->
    case vs of {
     [] -> Nothing;
     (:) v l ->
      case v of {
       BVal _ -> Nothing;
       RVal x ->
        case l of {
         [] -> Nothing;
         (:) v0 l0 ->
          case v0 of {
           BVal _ -> Nothing;
           RVal y ->
            case l0 of {
             [] -> Just (BVal ((<=) x y));
             (:) _ _ -> Nothing}}}}};
   Equal ->
    case vs of {
     [] -> Nothing;
     (:) v l ->
      case v of {
       BVal _ -> Nothing;
       RVal x ->
        case l of {
         [] -> Nothing;
         (:) v0 l0 ->
          case v0 of {
           BVal _ -> Nothing;
           RVal y ->
            case l0 of {
             [] -> Just (BVal ((==) x y));
             (:) _ _ -> Nothing}}}}};
   Not ->
    case vs of {
     [] -> Nothing;
     (:) v l ->
      case v of {
       BVal x ->
        case l of {
         [] -> Just (BVal (not x));
         (:) _ _ -> Nothing};
       RVal _ -> Nothing}};
   Neg ->
    case vs of {
     [] -> Nothing;
     (:) v l ->
      case v of {
       BVal _ -> Nothing;
       RVal x ->
        case l of {
         [] -> Just (RVal ((-) 0 x));
         (:) _ _ -> Nothing}}};
   BLit b ->
    case vs of {
     [] -> Just (BVal b);
     (:) _ _ -> Nothing};
   RLit r ->
    case vs of {
     [] -> Just (RVal r);
     (:) _ _ -> Nothing};
   Cond ->
    case vs of {
     [] -> Nothing;
     (:) v l ->
      case v of {
       BVal b ->
        case l of {
         [] -> Nothing;
         (:) v0 l0 ->
          case v0 of {
           BVal x ->
            case l0 of {
             [] -> Nothing;
             (:) v1 l1 ->
              case v1 of {
               BVal y ->
                case l1 of {
                 [] -> Just (BVal
                  (case b of {
                    True -> x;
                    False -> y}));
                 (:) _ _ -> Nothing};
               RVal _ -> Nothing}};
           RVal x ->
            case l0 of {
             [] -> Nothing;
             (:) v1 l1 ->
              case v1 of {
               BVal _ -> Nothing;
               RVal y ->
                case l1 of {
                 [] -> Just (RVal
                  (case b of {
                    True -> x;
                    False -> y}));
                 (:) _ _ -> Nothing}}}}};
       RVal _ -> Nothing}}}

texprSem :: TExpr -> TEnv -> Int
texprSem e tenv =
  case e of {
   Tvar v -> tenv v;
   Tnum n -> n}

translateExp :: Int -> Exp -> Exp
translateExp d e =
  case e of {
   OpE op args -> OpE op (P.map (translateExp d) args);
   Obs l i -> Obs l ((+) d i);
   VarE a -> VarE a;
   Acc f n z -> Acc (translateExp d f) n (translateExp d z)}

data TimeB =
   Time Int
 | TimeBot

tleb :: TimeB -> TimeB -> Bool
tleb t1 t2 =
  case t1 of {
   Time t1' ->
    case t2 of {
     Time t2' -> (<=) t1' t2';
     TimeBot -> False};
   TimeBot -> True}

tadd :: Int -> TimeB -> TimeB
tadd d t =
  case t of {
   Time t' -> Time ((+) t' d);
   TimeBot -> TimeBot}

tsub :: Int -> TimeB -> TimeB
tsub d =
  tadd (negate d)

tadd' :: Int -> TimeB -> TimeB
tadd' d =
  tadd (id d)

tsub' :: Int -> TimeB -> TimeB
tsub' d =
  tsub (id d)

inst_contr :: Contr -> TEnv -> Contr
inst_contr c tenv =
  case c of {
   Let e c' -> Let e (inst_contr c' tenv);
   Scale e c' -> Scale e (inst_contr c' tenv);
   Translate texp c' -> Translate (Tnum (texprSem texp tenv))
    (inst_contr c' tenv);
   Both c' c'' -> Both (inst_contr c' tenv) (inst_contr c'' tenv);
   If e texp c' c'' -> If e (Tnum (texprSem texp tenv)) (inst_contr c' tenv)
    (inst_contr c'' tenv);
   x -> x}

data TiTy =
   TimedType Ty TimeB

time :: TiTy -> TimeB
time t =
  case t of {
   TimedType _ ti -> ti}

type0 :: TiTy -> Ty
type0 t =
  case t of {
   TimedType ty _ -> ty}

add_time :: Int -> TiTy -> TiTy
add_time d t =
  case t of {
   TimedType ty ti -> TimedType ty (tadd' d ti)}

sub_time :: Int -> TiTy -> TiTy
sub_time d t =
  case t of {
   TimedType ty ti -> TimedType ty (tsub' d ti)}

type TiTyEnv = Env' TiTy

inferObs :: ObsLabel -> Ty
inferObs l =
  case l of {
   LabR _ -> REAL;
   LabB _ -> BOOL}

tyeqb :: Ty -> Ty -> Bool
tyeqb t1 t2 =
  case t1 of {
   REAL ->
    case t2 of {
     REAL -> True;
     BOOL -> False};
   BOOL ->
    case t2 of {
     REAL -> False;
     BOOL -> True}}

inferOp :: Op -> (List Ty) -> Maybe Ty
inferOp op args =
  case op of {
   And ->
    case args of {
     [] -> Nothing;
     (:) t l ->
      case t of {
       REAL -> Nothing;
       BOOL ->
        case l of {
         [] -> Nothing;
         (:) t0 l0 ->
          case t0 of {
           REAL -> Nothing;
           BOOL ->
            case l0 of {
             [] -> Just BOOL;
             (:) _ _ -> Nothing}}}}};
   Or ->
    case args of {
     [] -> Nothing;
     (:) t l ->
      case t of {
       REAL -> Nothing;
       BOOL ->
        case l of {
         [] -> Nothing;
         (:) t0 l0 ->
          case t0 of {
           REAL -> Nothing;
           BOOL ->
            case l0 of {
             [] -> Just BOOL;
             (:) _ _ -> Nothing}}}}};
   Less ->
    case args of {
     [] -> Nothing;
     (:) t l ->
      case t of {
       REAL ->
        case l of {
         [] -> Nothing;
         (:) t0 l0 ->
          case t0 of {
           REAL ->
            case l0 of {
             [] -> Just BOOL;
             (:) _ _ -> Nothing};
           BOOL -> Nothing}};
       BOOL -> Nothing}};
   Leq ->
    case args of {
     [] -> Nothing;
     (:) t l ->
      case t of {
       REAL ->
        case l of {
         [] -> Nothing;
         (:) t0 l0 ->
          case t0 of {
           REAL ->
            case l0 of {
             [] -> Just BOOL;
             (:) _ _ -> Nothing};
           BOOL -> Nothing}};
       BOOL -> Nothing}};
   Equal ->
    case args of {
     [] -> Nothing;
     (:) t l ->
      case t of {
       REAL ->
        case l of {
         [] -> Nothing;
         (:) t0 l0 ->
          case t0 of {
           REAL ->
            case l0 of {
             [] -> Just BOOL;
             (:) _ _ -> Nothing};
           BOOL -> Nothing}};
       BOOL -> Nothing}};
   Not ->
    case args of {
     [] -> Nothing;
     (:) t l ->
      case t of {
       REAL -> Nothing;
       BOOL ->
        case l of {
         [] -> Just BOOL;
         (:) _ _ -> Nothing}}};
   Neg ->
    case args of {
     [] -> Nothing;
     (:) t l ->
      case t of {
       REAL ->
        case l of {
         [] -> Just REAL;
         (:) _ _ -> Nothing};
       BOOL -> Nothing}};
   BLit _ ->
    case args of {
     [] -> Just BOOL;
     (:) _ _ -> Nothing};
   RLit _ ->
    case args of {
     [] -> Just REAL;
     (:) _ _ -> Nothing};
   Cond ->
    case args of {
     [] -> Nothing;
     (:) t l ->
      case t of {
       REAL -> Nothing;
       BOOL ->
        case l of {
         [] -> Nothing;
         (:) t1 l0 ->
          case l0 of {
           [] -> Nothing;
           (:) t2 l1 ->
            case l1 of {
             [] ->
              case tyeqb t1 t2 of {
               True -> Just t1;
               False -> Nothing};
             (:) _ _ -> Nothing}}}}};
   _ ->
    case args of {
     [] -> Nothing;
     (:) t l ->
      case t of {
       REAL ->
        case l of {
         [] -> Nothing;
         (:) t0 l0 ->
          case t0 of {
           REAL ->
            case l0 of {
             [] -> Just REAL;
             (:) _ _ -> Nothing};
           BOOL -> Nothing}};
       BOOL -> Nothing}}}

tmax :: TimeB -> TimeB -> TimeB
tmax t1 t2 =
  case t1 of {
   Time t1' ->
    case t2 of {
     Time t2' -> Time (max t1' t2');
     TimeBot -> t1};
   TimeBot -> t2}

tmaxs :: (List TimeB) -> TimeB
tmaxs ts =
  foldr tmax TimeBot ts

inferE :: TiTyEnv -> Exp -> Maybe TiTy
inferE env e =
  case e of {
   OpE op args ->
    (>>=) (sequence (P.map (inferE env) args)) (\args' ->
      liftM (\ty -> TimedType ty (tmaxs (P.map time args')))
        (inferOp op (P.map type0 args')));
   Obs l i -> Just (TimedType (inferObs l) (Time i));
   VarE v -> lookupEnv v env;
   Acc f d z ->
    (>>=) (inferE (P.map (add_time d) env) z) (\t ->
      (>>=) (inferE ((:) (TimedType (type0 t) TimeBot) env) f) (\t' ->
        case tyeqb (type0 t) (type0 t') of {
         True -> Just (TimedType (type0 t)
          (tmax (tsub' d (time t)) (time t')));
         False -> Nothing}))}

data TimeI =
   Time' TimeB
 | TimeTop

iadd :: Int -> TimeI -> TimeI
iadd d t =
  case t of {
   Time' t' -> Time' (tadd' d t');
   TimeTop -> TimeTop}

tileb :: TimeB -> TimeI -> Bool
tileb l t =
  case t of {
   Time' t' -> tleb l t';
   TimeTop -> True}

ileb :: TimeI -> TimeI -> Bool
ileb t1 t2 =
  case t1 of {
   Time' s1 ->
    case t2 of {
     Time' s2 -> tleb s1 s2;
     TimeTop -> True};
   TimeTop ->
    case t2 of {
     Time' _ -> False;
     TimeTop -> True}}

imin :: TimeI -> TimeI -> TimeI
imin t1 t2 =
  case ileb t1 t2 of {
   True -> t1;
   False -> t2}

inferC :: TiTyEnv -> TEnv -> Contr -> Maybe TimeI
inferC env tenv c =
  case c of {
   Zero -> Just TimeTop;
   Let e c' -> (>>=) (inferE env e) (\t -> inferC ((:) t env) tenv c');
   Transfer _ _ _ -> Just (Time' (Time 0));
   Scale e c' ->
    (>>=) (inferE env e) (\ty ->
      (>>=) (inferC env tenv c') (\t ->
        case (&&) (tyeqb (type0 ty) REAL) (tileb (time ty) t) of {
         True -> Just t;
         False -> Nothing}));
   Translate d c' ->
    liftM (iadd (texprSem d tenv))
      (inferC (P.map (sub_time (texprSem d tenv)) env) tenv c');
   Both c1 c2 -> liftM2 imin (inferC env tenv c1) (inferC env tenv c2);
   If e d c1 c2 ->
    (>>=) (inferE env e) (\t ->
      case (&&) (tyeqb (type0 t) BOOL) (tleb (time t) (Time 0)) of {
       True ->
        liftM2 imin (inferC env tenv c1)
          (liftM (iadd (texprSem d tenv))
            (inferC (P.map (sub_time (texprSem d tenv)) env) tenv c2));
       False -> Nothing})}

has_type :: TEnv -> Contr -> Bool
has_type tenv c =
  case inferC [] tenv c of {
   Just _ -> True;
   Nothing -> False}

type ExtEnvP = ExtEnv' (Maybe Val)

type EnvP = List (Maybe Val)

fromLit :: Exp -> Maybe Val
fromLit e =
  case e of {
   OpE op args ->
    case op of {
     BLit b ->
      case args of {
       [] -> Just (BVal b);
       (:) _ _ -> Nothing};
     RLit r ->
      case args of {
       [] -> Just (RVal r);
       (:) _ _ -> Nothing};
     _ -> Nothing};
   _ -> Nothing}

toLit :: Val -> Exp
toLit e =
  case e of {
   BVal b -> OpE (BLit b) [];
   RVal r -> OpE (RLit r) []}

fromBLit :: Exp -> Maybe Bool
fromBLit e =
  case e of {
   OpE op args ->
    case op of {
     BLit b ->
      case args of {
       [] -> Just b;
       (:) _ _ -> Nothing};
     _ -> Nothing};
   _ -> Nothing}

fromRLit :: Exp -> Maybe Double
fromRLit e =
  case e of {
   OpE op args ->
    case op of {
     RLit r ->
      case args of {
       [] -> Just r;
       (:) _ _ -> Nothing};
     _ -> Nothing};
   _ -> Nothing}

isZeroLit :: Exp -> Bool
isZeroLit e =
  case e of {
   OpE op args ->
    case op of {
     RLit r ->
      case args of {
       [] -> (==) r 0;
       (:) _ _ -> False};
     _ -> False};
   _ -> False}

isOneLit :: Exp -> Bool
isOneLit e =
  case e of {
   OpE op args ->
    case op of {
     RLit r ->
      case args of {
       [] -> (==) r 1;
       (:) _ _ -> False};
     _ -> False};
   _ -> False}

specialiseOpSimp :: Op -> (List Exp) -> Maybe Exp
specialiseOpSimp op args =
  liftM toLit ((>>=) (mapM fromLit args) (opSem op))

specialiseOp :: Op -> (List Exp) -> Maybe Exp
specialiseOp op args =
  case op of {
   Add ->
    case args of {
     [] -> Nothing;
     (:) e1 l ->
      case l of {
       [] -> Nothing;
       (:) e2 l0 ->
        case l0 of {
         [] ->
          case isZeroLit e1 of {
           True -> Just e2;
           False ->
            case isZeroLit e2 of {
             True -> Just e1;
             False -> specialiseOpSimp op args}};
         (:) _ _ -> Nothing}}};
   Mult ->
    case args of {
     [] -> Nothing;
     (:) e1 l ->
      case l of {
       [] -> Nothing;
       (:) e2 l0 ->
        case l0 of {
         [] ->
          case isOneLit e1 of {
           True -> Just e2;
           False ->
            case isOneLit e2 of {
             True -> Just e1;
             False ->
              case (||) (isZeroLit e1) (isZeroLit e2) of {
               True -> Just (OpE (RLit 0) []);
               False -> specialiseOpSimp op args}}};
         (:) _ _ -> Nothing}}};
   And ->
    case args of {
     [] -> Nothing;
     (:) e1 l ->
      case l of {
       [] -> Nothing;
       (:) e2 l0 ->
        case l0 of {
         [] ->
          case fromBLit e1 of {
           Just b ->
            case b of {
             True -> Just e2;
             False -> Just e1};
           Nothing ->
            case fromBLit e2 of {
             Just b ->
              case b of {
               True -> Just e1;
               False -> Just e2};
             Nothing -> Nothing}};
         (:) _ _ -> Nothing}}};
   Or ->
    case args of {
     [] -> Nothing;
     (:) e1 l ->
      case l of {
       [] -> Nothing;
       (:) e2 l0 ->
        case l0 of {
         [] ->
          case fromBLit e1 of {
           Just b ->
            case b of {
             True -> Just e1;
             False -> Just e2};
           Nothing ->
            case fromBLit e2 of {
             Just b ->
              case b of {
               True -> Just e2;
               False -> Just e1};
             Nothing -> Nothing}};
         (:) _ _ -> Nothing}}};
   Cond ->
    case args of {
     [] -> Nothing;
     (:) e1 l ->
      case l of {
       [] -> Nothing;
       (:) e2 l0 ->
        case l0 of {
         [] -> Nothing;
         (:) e3 l1 ->
          case l1 of {
           [] ->
            case fromBLit e1 of {
             Just b ->
              case b of {
               True -> Just e2;
               False -> Just e3};
             Nothing -> Nothing};
           (:) _ _ -> Nothing}}}};
   _ -> specialiseOpSimp op args}

lookupEnvP :: Var -> EnvP -> Maybe Val
lookupEnvP v env =
  case v of {
   V1 ->
    case env of {
     [] -> Nothing;
     (:) x _ -> x};
   VS v0 ->
    case env of {
     [] -> Nothing;
     (:) _ xs -> lookupEnvP v0 xs}}

specialiseFun :: ((List (Maybe Val)) -> (ExtEnv' (Maybe Val)) -> Exp) -> EnvP
                 -> ExtEnvP -> Int -> (Maybe Val) -> Maybe Val
specialiseFun f env ext l r =
  fromLit (f ((:) r env) (adv_ext (id l) ext))

specialiseExp :: Exp -> EnvP -> ExtEnvP -> Exp
specialiseExp e env ext =
  case e of {
   OpE op args ->
    let {args' = P.map (\e' -> specialiseExp e' env ext) args} in
    fromMaybe (OpE op args') (specialiseOp op args');
   Obs obs t -> fromMaybe e (liftM toLit (ext obs t));
   VarE v -> fromMaybe e (liftM toLit (lookupEnvP v env));
   Acc f l z ->
    let {ext' = adv_ext (negate (id l)) ext} in
    let {ze = specialiseExp z env ext'} in
    let {z' = fromLit ze} in
    let {f' = specialiseFun (specialiseExp f) env ext'} in
    fromMaybe (Acc f l ze) (liftM toLit (acc_sem f' l z'))}

elimVarV :: Var -> Var -> Maybe Var
elimVarV v1 v2 =
  case v1 of {
   V1 ->
    case v2 of {
     V1 -> Nothing;
     VS v2' -> Just v2'};
   VS v1' ->
    case v2 of {
     V1 -> Just V1;
     VS v2' -> liftM (\x -> VS x) (elimVarV v1' v2')}}

elimVarE :: Var -> Exp -> Maybe Exp
elimVarE v e =
  case e of {
   OpE op args -> liftM (\x -> OpE op x) (sequence (P.map (elimVarE v) args));
   Obs _ _ -> Just e;
   VarE v' -> liftM (\x -> VarE x) (elimVarV v v');
   Acc e1 l e2 ->
    liftM2 (\e1' e2' -> Acc e1' l e2') (elimVarE (VS v) e1) (elimVarE v e2)}

elimVarC :: Var -> Contr -> Maybe Contr
elimVarC v c =
  case c of {
   Let e c' -> liftM2 (\x x0 -> Let x x0) (elimVarE v e) (elimVarC (VS v) c');
   Scale e c' -> liftM2 (\x x0 -> Scale x x0) (elimVarE v e) (elimVarC v c');
   Translate l c' -> liftM (\x -> Translate l x) (elimVarC v c');
   Both c1 c2 -> liftM2 (\x x0 -> Both x x0) (elimVarC v c1) (elimVarC v c2);
   If e l c1 c2 ->
    liftM3 (\e' c1' c2' -> If e' l c1' c2') (elimVarE v e) (elimVarC v c1)
      (elimVarC v c2);
   _ -> Just c}

smartLet :: Exp -> Contr -> Contr
smartLet e c =
  case elimVarC V1 c of {
   Just c' -> c';
   Nothing -> Let e c}

smartScale :: Exp -> Contr -> Contr
smartScale e c =
  case isZeroLit e of {
   True -> Zero;
   False ->
    case c of {
     Zero -> Zero;
     _ -> Scale e c}}

smartBoth :: Contr -> Contr -> Contr
smartBoth c1 c2 =
  case c1 of {
   Zero -> c2;
   _ ->
    case c2 of {
     Zero -> c1;
     _ -> Both c1 c2}}

smartTranslate :: Int -> Contr -> Contr
smartTranslate l c =
  (\fO fS n -> if n==0 then fO () else fS (n-1))
    (\_ ->
    c)
    (\_ ->
    case c of {
     Zero -> Zero;
     _ -> Translate (Tnum l) c})
    l

traverseIf :: EnvP -> ExtEnvP -> Exp -> (ExtEnvP -> Contr) -> (ExtEnvP ->
              Contr) -> Int -> Int -> Maybe Contr
traverseIf env ext e c1 c2 d l =
  case fromBLit (specialiseExp e env ext) of {
   Just b ->
    case b of {
     True -> Just (smartTranslate d (c1 ext));
     False ->
      (\fO fS n -> if n==0 then fO () else fS (n-1))
        (\_ -> Just
        (smartTranslate d (c2 ext)))
        (\l' ->
        traverseIf env (adv_ext (id 1) ext) e c1 c2 (succ d) l')
        l};
   Nothing -> Nothing}

specialise :: Contr -> EnvP -> TEnv -> ExtEnvP -> Contr
specialise c env tenv ext =
  case c of {
   Let e c' ->
    let {e' = specialiseExp e env ext} in
    smartLet e' (specialise c' ((:) (fromLit e') env) tenv ext);
   Scale e c' ->
    smartScale (specialiseExp e env ext) (specialise c' env tenv ext);
   Translate l c' ->
    let {t' = texprSem l tenv} in
    smartTranslate t' (specialise c' env tenv (adv_ext (id t') ext));
   Both c1 c2 ->
    smartBoth (specialise c1 env tenv ext) (specialise c2 env tenv ext);
   If e l c1 c2 ->
    fromMaybe c
      (traverseIf env ext e (specialise c1 env tenv) (specialise c2 env tenv)
        0 (texprSem l tenv));
   _ -> c}

type Key = (,) ((,) Party Party) Asset

singleton :: Key -> Double -> FMap
singleton k r =
  Map.insert k r Map.empty

compare1 :: Party -> Party -> Ordering
compare1 =
  Prelude.error "AXIOM TO BE REALIZED"

type SMap =
  FMap
  -- singleton inductive, whose constructor was mkSMap
  
getFMap :: SMap -> FMap
getFMap sm =
  sm

map :: (Double -> Double) -> SMap -> SMap
map f sm =
  Map.map f sm

union_with :: (Double -> Double -> Double) -> SMap -> SMap -> SMap
union_with f sm1 sm2 =
  unionWith (\x y ->
    let {r = f x y} in
    case (==) r 0 of {
     True -> Nothing;
     False -> Just r}) sm1 sm2

singleton0 :: Party -> Party -> Asset -> Double -> SMap
singleton0 p1 p2 a r =
  let {filtered_var = compare1 p1 p2} in
  case filtered_var of {
   EQ -> Map.empty;
   LT -> singleton ((,) ((,) p1 p2) a) r;
   GT -> singleton ((,) ((,) p2 p1) a) (negate r)}

is_empty :: SMap -> Bool
is_empty sm =
  Map.null (getFMap sm)

empty :: SMap
empty =
  Map.empty

scale_trans' :: (Maybe Double) -> SMap -> Maybe SMap
scale_trans' v t =
  case v of {
   Just v0 -> Just
    (case (==) v0 0 of {
      True -> empty;
      False -> map (\x -> (*) v0 x) t});
   Nothing ->
    case is_empty t of {
     True -> Just empty;
     False -> Nothing}}

redfun :: Contr -> EnvP -> ExtEnvP -> TEnv -> Maybe ((,) Contr SMap)
redfun c env ext tenv =
  case c of {
   Zero -> Just ((,) Zero empty);
   Let e c0 ->
    let {e' = specialiseExp e env ext} in
    liftM (\ct ->
      case ct of {
       (,) c' t -> (,) (smartLet (translateExp (negate 1) e') c') t})
      (redfun c0 ((:) (fromLit e') env) ext tenv);
   Transfer c0 p1 p2 -> Just ((,) Zero (singleton0 c0 p1 p2 1));
   Scale e c0 ->
    let {e' = specialiseExp e env ext} in
    (>>=) (redfun c0 env ext tenv) (\ct ->
      case ct of {
       (,) c' t ->
        liftM (\t' -> (,) (smartScale (translateExp (negate 1) e') c') t')
          (scale_trans' (fromRLit e') t)});
   Translate d c0 ->
    (\fO fS n -> if n==0 then fO () else fS (n-1))
      (\_ ->
      redfun c0 env ext tenv)
      (\n' -> Just ((,) (Translate (Tnum n') c0)
      empty))
      (texprSem d tenv);
   Both c1 c2 ->
    liftM2 (\ct1 ct2 ->
      case ct1 of {
       (,) c1' t1 ->
        case ct2 of {
         (,) c2' t2 -> (,) (smartBoth c1' c2') (union_with (+) t1 t2)}})
      (redfun c1 env ext tenv) (redfun c2 env ext tenv);
   If b d c1 c2 ->
    (>>=) (fromBLit (specialiseExp b env ext)) (\b' ->
      case b' of {
       True -> redfun c1 env ext tenv;
       False ->
        (\fO fS n -> if n==0 then fO () else fS (n-1))
          (\_ ->
          redfun c2 env ext tenv)
          (\n' -> Just ((,) (If b (Tnum n') c1 c2)
          empty))
          (texprSem d tenv)})}

plus0 :: Int -> Int -> Int
plus0 n m =
  (\fO fS n -> if n==0 then fO () else fS (n-1))
    (\_ ->
    0)
    (\_ ->
    (+) n m)
    m

horizon :: Contr -> TEnv -> Int
horizon c tenv =
  case c of {
   Zero -> 0;
   Let _ c' -> horizon c' tenv;
   Transfer _ _ _ -> succ 0;
   Scale _ c' -> horizon c' tenv;
   Translate v c' -> plus0 (texprSem v tenv) (horizon c' tenv);
   Both c1 c2 -> max (horizon c1 tenv) (horizon c2 tenv);
   If _ l c1 c2 ->
    plus0 (texprSem l tenv) (max (horizon c1 tenv) (horizon c2 tenv))}
