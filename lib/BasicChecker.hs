{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use record patterns" #-}

module BasicChecker where

import Control.Lens (makeLenses, (%~), (^.))
import Control.Monad.State
import Data.Functor ((<&>))
import Data.List (intercalate)
import Debug.Trace (trace, traceM)
import Refinements (RTyp, SubC (..), Var)
import Util

-- Syntax for STLC with QF-UFLIA

binder :: String
binder = "nu"

type FnName = String

data Program = Program {_decls :: Table FnName Type, _bodies :: Table FnName Term}

emptyProgram :: Program
emptyProgram = Program (emptyTable Nothing) (emptyTable Nothing)

data Constant
  = CNOp InterpOp
  | CNInt Int
  | CNBool Bool
  deriving (Eq)

instance Show Constant where
  show (CNOp op) = show op
  show (CNInt i) = show i
  show (CNBool b) = show b

type Variable = String

type Binder = String

data InterpOp
  = Equal
  | Add
  | Sub
  | Leq
  | Lt
  | Geq
  | Gt
  deriving (Eq)

instance Show InterpOp where
  show Equal = "="
  show Add = "+"
  show Sub = "-"
  show Leq = "<="
  show Geq = ">="
  show Lt = "<"
  show Gt = ">"

data Term
  = TConst Constant
  | TVar Variable
  | TLet Variable Term Term
  | TLam Variable Term
  | TApp Term Variable
  | TAnn Term Type
  | TCond Variable Term Term
  | TRec Variable Term Type Term
  | TTAbs TypeVariable Kind Term
  | TTApp Term BareType
  deriving (Eq)

instance Show Term where
  show (TConst c) = show c
  show (TVar v) = v
  show (TLet v bound body) = "let " ++ v ++ " = (" ++ show bound ++ ") in " ++ show body
  show (TLam v body) = "lambda " ++ v ++ ". (" ++ show body ++ ")"
  show (TApp term v) = "(" ++ show term ++ ") " ++ v
  show (TAnn term typ) = "(" ++ show term ++ ") : " ++ show typ
  show (TCond v tt tf) = "if (" ++ v ++ ") then (" ++ show tt ++ ") else (" ++ show tf ++ ")"
  show (TRec x e t e1) = "rec " ++ x ++ " = (" ++ show e ++ ") : " ++ show t ++ " in (" ++ show e1 ++ ")"
  show (TTAbs tv k t) = "Lambda " ++ tv ++ " : " ++ show k ++ ". (" ++ show t ++ ")"
  show (TTApp t bt) = "(" ++ show t ++ ")[" ++ show bt ++ "]"

data HornVariable
  = HornVariable Variable BasicType [Type]
  deriving (Eq)

instance Show HornVariable where
  -- This is way too verbose?
  show :: HornVariable -> String
  show (HornVariable v b tys) = "kappa{" ++ v ++ "}@(" ++ show b ++ " | " ++ intercalate ", " (fmap show tys) ++ ")"

-- show (HornVariable v b tys) = "kappa{" ++ v ++ "}"

data Predicate
  = PVar Variable
  | PBool Bool
  | PInt Int
  | PInterpOp InterpOp Predicate Predicate
  | PAnd Predicate Predicate
  | POr Predicate Predicate
  | PNeg Predicate
  | -- | PIf Predicate Predicate Predicate
    PUninterpFun Variable Predicate -- ??
  | PHornApp HornVariable [Variable]
  deriving (Eq)

instance Show Predicate where
  show (PVar v) = v
  show (PBool b) = show b
  show (PInt i) = show i
  show (PInterpOp op p0 p1) = show p0 ++ " " ++ show op ++ " " ++ show p1
  show (PAnd p0 p1) = show p0 ++ " && " ++ show p1
  show (POr p0 p1) = show p0 ++ " || " ++ show p1
  show (PNeg p) = "!(" ++ show p ++ ")"
  show (PUninterpFun v p) = v ++ "(" ++ show p ++ ")"
  show (PHornApp h vs) = show h ++ "(" ++ intercalate ", " vs ++ ")"

data Constraint
  = CPred Predicate
  | CAnd Constraint Constraint
  | CFun Variable BasicType Predicate Constraint -- forall x: b. p => c
  deriving
    (Eq)

instance Show Constraint where
  show (CPred p) = show p
  show (CAnd p0 p1) = "(" ++ show p0 ++ ") && (" ++ show p1 ++ ")"
  show (CFun v b p c) = "forall " ++ v ++ ": " ++ show b ++ ". (" ++ show p ++ ") => " ++ show c

-- show (CImp v t c) = "(" ++ v ++ " :: " ++ show t ++ ") => " ++ show c

data BasicType
  = BInt
  | BBool
  | BTVar TypeVariable
  deriving (Eq)

instance Show BasicType where
  show BInt = "int"
  show BBool = "bool"
  show (BTVar x) = x

data Refinement
  = RKnown Predicate
  | Hole
  deriving (Eq)

instance Show Refinement where
  show (RKnown p) = "{" ++ binder ++ ": " ++ show p ++ "}"
  show Hole = "{*}"

data Type
  = TRBase BasicType Refinement
  | TDepFn Variable Type Type
  | TForall TypeVariable Kind Type
  deriving (Eq)

instance Show Type where
  show (TRBase b (RKnown (PBool True))) = show b
  show (TRBase b r) = show b ++ show r
  show (TDepFn v t s) = v ++ ":" ++ show t ++ " -> " ++ show s
  show (TForall tv k t) = "forall " ++ tv ++ " : " ++ show k ++ ". (" ++ show t ++ ")"

-- BareTypes are a subtype of Types, where base variables are all refined with holes.
-- We do not need to distinguish between these cases in the code.
type BareType = Type

------ functional contexts

data Kind = BaseKind | StarKind deriving (Eq, Show)

type TypeVariable = String

data Context = Context {_terms :: Table Variable Type, _types :: Table TypeVariable Kind}
  deriving (Show)

-- Datatype lenses
makeLenses ''Context
makeLenses ''Program

instance Show Program where
  show p = intercalate "\n" (typeDecls ++ bodyDecls)
    where
      typeDecls = (concatMap doShowDecl . bToList) (p ^. decls . dom)
      bodyDecls = (concatMap doShowBody . bToList) (p ^. bodies . dom)

      doShowDecl :: FnName -> [String]
      doShowDecl fn = showTyDecl fn : ([showBodyDecl fn | hasBody fn])

      doShowBody :: FnName -> [String]
      doShowBody fn = [showBodyDecl fn | not (hasTy fn)]

      showTyDecl fn = "val " ++ fn ++ " : " ++ show (getTbl (p ^. decls) fn)
      showBodyDecl fn = "let " ++ fn ++ " = " ++ show (getTbl (p ^. bodies) fn)

      hasBody x = bContains x (p ^. (bodies . dom))
      hasTy x = bContains x (p ^. decls . dom)

------ abbreviations
-- b        abbreviates   b{v: true}
base :: BasicType -> Type
base b = TRBase b (trefine (PBool True))

-- {v:p}    abbreviates   b{v: p}             (when b is clear)
-- b{p}     abbreviates   b{v: p}             (when p doesn't use the binder v)
trefine :: Predicate -> Refinement
trefine = RKnown

------ primitive types
-- primitive types for all constants
prim :: Constant -> Type
prim (CNInt i) = iprim i
prim (CNOp op) = oprim op
prim (CNBool True) = TRBase BBool $ RKnown (PVar binder)
prim (CNBool False) = TRBase BBool $ RKnown $ PNeg (PVar binder)

-- iprim(i) := int(v: v == i)
iprim :: Int -> Type
iprim = TRBase BInt . RKnown . PInterpOp Equal (PVar "v") . PInt

-- oprim(op) := x:int -> (y:int -> int{v: v=x+y})
oprim :: InterpOp -> Type
oprim Add = mkOprim Add
oprim Sub = mkOprim Sub
oprim Equal = mkOprim Equal
oprim Leq = mkOprim Leq
oprim Lt = mkOprim Lt
oprim Geq = mkOprim Geq
oprim Gt = mkOprim Gt

-- fixme: equal is still a little f***ed

mkOprim op =
  TDepFn "x" (base BInt) $
    TDepFn "y" (base BInt) $
      TRBase (brt op) (RKnown (PInterpOp Equal (PVar binder) (PInterpOp op (PVar "x") (PVar "y"))))
  where
    brt Add = BInt
    brt Sub = BInt
    brt Equal = error "amongus"
    brt Leq = BBool
    brt Lt = BBool
    brt Geq = BBool
    brt Gt = BBool

class Subst a where
  subst :: a -> Variable -> Predicate -> a

instance Subst Predicate where
  -- TODO: There has to be a better way to do this
  subst :: Predicate -> Variable -> Predicate -> Predicate
  subst p@(PVar v0) v1 p1
    | v0 == v1 = p1
    | otherwise = p
  subst p@(PBool _) _ _ = p
  subst p@(PInt _) _ _ = p
  subst (PInterpOp op p0 p1) v p = PInterpOp op (subst p0 v p) (subst p1 v p)
  subst (PAnd p0 p1) v p = PAnd (subst p0 v p) (subst p1 v p)
  subst (POr p0 p1) v p = POr (subst p0 v p) (subst p1 v p)
  subst (PNeg p0) v p = PNeg (subst p0 v p)
  subst (PUninterpFun f p1) v p = PUninterpFun f (subst p v p1)
  subst x@(PHornApp h vs) _ _ = x -- this is... probably unsound?

------ shorthand: implication constraints
cimp :: Variable -> Type -> Constraint -> Constraint
cimp x (TRBase b (RKnown p)) c = CFun x b (subst p binder (PVar x)) c
cimp _ _ c = c

instance Subst Constraint where
  subst = undefined

instance Subst Type where
  subst t0@(TRBase b (RKnown p)) y z
    | binder == y = t0
    | otherwise = TRBase b (RKnown (subst p y z))
  subst (TDepFn x s t) y z
    | x == y = TDepFn x (subst s x z) t
    | otherwise = TDepFn x (subst s y z) (subst t y z)

substTyVar :: TypeVariable -> Type -> Type -> Type
substTyVar aFrom tTo (TRBase (BTVar alpha) r)
  | alpha == aFrom = tTo
  | otherwise = TRBase (BTVar alpha) r
substTyVar aFrom tTo (TDepFn v t1 t2) = TDepFn v (substTyVar aFrom tTo t1) (substTyVar aFrom tTo t2)
substTyVar aFrom tTo (TForall tv k t)
  | tv == aFrom = TForall tv k t
  | otherwise = TForall tv k (substTyVar aFrom tTo t)

-- Algorithmic subtyping: Generate Imp Constraints
subKappa :: Type -> Type -> Gen [SubC]
subKappa (TForall alpha1 k1 t1) (TForall alpha2 k2 t2)
  -- Type abstraction: Replace the type variables and enter
  | k1 == k2 = subKappa t1 (substTyVar alpha2 (base (BTVar alpha1)) t2)
subKappa x@(TRBase b0 (RKnown p1)) y@(TRBase b1 (RKnown p2))
  | b0 == b1 = do
      freshVar <- gensym
      return [SubC [] (coerceRTyp x) (coerceRTyp y)]
subKappa (TDepFn x1 s1 t1) (TDepFn x2 s2 t2) = do
  ci <- subKappa s2 s1
  co <- subKappa (subst t1 x1 (PVar x2)) t2
  return $ ci ++ cimpKappa x2 (coerceRTyp s2) co
subKappa t1 t2 = trace ("sub of " ++ show t1 ++ " <: " ++ show t2 ++ " undefined") undefined

cimpKappa :: Variable -> RTyp -> [SubC] -> [SubC]
cimpKappa v ty ss = fmap (addAssumption (v, ty)) ss
  where
    addAssumption :: (Var, RTyp) -> SubC -> SubC
    addAssumption z (SubC gs x y) = SubC (z : gs) x y

coerceRTyp :: Type -> RTyp
coerceRTyp (TForall _ _ _) = error "cannot coerce Forall to a RTyp"
coerceRTyp (TRBase b0 (RKnown p1)) = error "wip coerce rtyp"

sub :: Type -> Type -> Gen Constraint
sub (TForall alpha1 k1 t1) (TForall alpha2 k2 t2)
  | k1 == k2 = sub t1 (substTyVar alpha2 (base (BTVar alpha1)) t2)
sub (TRBase b0 (RKnown p1)) (TRBase b1 (RKnown p2))
  | b0 == b1 = do
      freshVar <- gensym
      return $ CFun freshVar b0 p1 (CPred (subst p2 binder (PVar freshVar)))
sub (TDepFn x1 s1 t1) (TDepFn x2 s2 t2) = do
  ci <- sub s2 s1
  co <- sub (subst t1 x1 (PVar x2)) t2
  return $ CAnd ci (cimp x2 s2 co)
sub t1 t2 = trace ("sub of " ++ show t1 ++ " <: " ++ show t2 ++ " undefined") undefined

-- Algorithmic state

newtype ConstraintState = ConstraintState {_next_fresh :: Int}

defaultState :: ConstraintState
defaultState = ConstraintState 0

type Gen = State ConstraintState

gensym :: Gen String
gensym = do
  s <- get
  let (ConstraintState r) = s
  put $ s {_next_fresh = r + 1}
  return $ "tmp." ++ show r

-- Constraint synthesis (fixme: abstract this with the non-inference version)
synthC :: Context -> Term -> Gen ([SubC], Type)
synthC c t = synth1 c t
  where
    synth1 g (TTApp e tau) = do
      t <- fresh g tau
      syn_e <- synthC g e
      let (c, TForall alpha k s) = syn_e
      return (c, substTyVar alpha t s)
    synth1 g (TVar x) = do
      return ([], self x (getTbl (g ^. terms) x))
    synth1 _ (TConst c) = do
      return ([], prim c)
    synth1 g (TApp e y) = do
      synR <- synthC g e
      let (c, TDepFn x s t) = synR
      c1 <- checkC g (TVar y) s
      return (c ++ c1, subst t x (PVar y))
    synth1 g (TAnn e s) = do
      t <- fresh g s
      c <- checkC g e t
      return (c, t)
    synth1 _ _ = undefined

-- Constraint checking (fixme: abstract this with the non-inference version)
checkC :: Context -> Term -> Type -> Gen [SubC]
checkC c t ty = check1 c t ty
  where
    check1 g (TTAbs alpha k e) (TForall a1 k1 t)
      | k == k1 && alpha == a1 = checkC (types %~ tblSet alpha k $ g) e t
    check1 g (TLam x e) (TDepFn x0 s t)
      | x == x0 = do
          c <- checkC (terms %~ tblSet x s $ g) e t
          return $ cimpKappa x (coerceRTyp s) c
    check1 g (TLet x e1 e2) t2 = do
      (c1, t1) <- synthC g e1
      c2 <- checkC (terms %~ tblSet x t1 $ g) e2 t2
      return $ c1 ++ (cimpKappa x (coerceRTyp t1) c2)
    check1 g (TCond x e1 e2) t = do
      y <- gensym
      c1 <- checkC g e1 t <&> cimpKappa y (coerceRTyp (TRBase BInt (trefine (PVar x))))
      c2 <- checkC g e2 t <&> cimpKappa y (coerceRTyp (TRBase BInt (trefine (PNeg (PVar x)))))
      return $ c1 ++ c2
    check1 g (TRec x e1 s1 e2) t = do
      t1 <- fresh g s1
      let g1 = terms %~ tblSet x t1 $ g
      c1 <- checkC g1 e1 t
      c2 <- checkC g1 e2 t
      return $ c1 ++ c2
    check1 g e t = do
      (c, s) <- synthC g e
      c1 <- subKappa s t
      return $ c ++ c1

-- Algorithmic synthesis
synth :: Context -> Term -> Gen (Constraint, Type)
synth c t = synth1 c t
  where
    synth1 g (TTApp e tau) = do
      -- traceM "[0/4 ttapp]"
      t <- fresh g tau
      -- traceM "[1/4 ttapp]"
      syn_e <- synth g e
      -- traceM "[2/4 ttapp]"
      let (c, TForall alpha k s) = syn_e
      -- traceM "[3/4 ttapp]"
      return (c, substTyVar alpha t s)
    synth1 g (TVar x) = do
      -- traceM "[0/1 tvar]"
      return (CPred $ PBool True, self x (getTbl (g ^. terms) x))
    -- chapter 3 version:
    -- return (CPred (PBool True), g x)
    synth1 _ (TConst c) = do
      -- traceM "[0/1 tconst]"
      return (CPred $ PBool True, prim c)
    synth1 g (TApp e y) = do
      -- traceM $ "[0/4 tapp]" ++ show (TApp e y)
      synR <- synth g e
      -- traceM "[1/4 tapp]"
      let (c, TDepFn x s t) = synR
      -- traceM "[2/4 tapp]"
      c1 <- check g (TVar y) s
      -- traceM "[3/4 tapp]"
      return (CAnd c c1, subst t x (PVar y))
    synth1 g (TAnn e s) = do
      -- traceM "[0/3 tann]"
      t <- fresh g s
      -- traceM "[1/3 tann]"
      c <- check g e t
      -- traceM "[2/3 tann]"
      return (c, t)
    synth1 _ _ = undefined

-- Algorithmic checking
check :: Context -> Term -> Type -> Gen Constraint
check c t ty = check1 c t ty
  where
    check1 g (TTAbs alpha k e) (TForall a1 k1 t)
      | k == k1 && alpha == a1 = check (types %~ tblSet alpha k $ g) e t
    check1 g (TLam x e) (TDepFn x0 s t)
      | x == x0 = do
          -- traceM "[0/2 tlet]"
          c <- check (terms %~ tblSet x s $ g) e t
          -- traceM "[1/2 tlet]"
          return $ cimp x s c
    check1 g (TLet x e1 e2) t2 = do
      -- traceM $ "[0/3 tlet]" ++ show (TLet x e1 e2)
      (c1, t1) <- synth g e1
      -- traceM "[1/3 tlet]"
      c2 <- check (terms %~ tblSet x t1 $ g) e2 t2
      -- traceM "[2/3 tlet]"
      return $ CAnd c1 (cimp x t1 c2)
    check1 g (TCond x e1 e2) t = do
      -- traceM "[0/4 tcond]"
      y <- gensym
      -- traceM "[1/4 tcond]"
      c1 <- check g e1 t <&> cimp y (TRBase BInt (trefine (PVar x)))
      -- traceM "[2/4 tcond]"
      c2 <- check g e2 t <&> cimp y (TRBase BInt (trefine (PNeg (PVar x))))
      -- traceM "[3/4 tcond]"
      return $ CAnd c1 c2
    check1 g (TRec x e1 s1 e2) t = do
      t1 <- fresh g s1
      let g1 = terms %~ tblSet x t1 $ g
      c1 <- check g1 e1 t
      c2 <- check g1 e2 t
      return $ CAnd c1 c2
    check1 g e t = do
      -- traceM "[0/3 checksynth]"
      (c, s) <- synth g e
      -- traceM "[1/3 checksynth]"
      c1 <- sub s t
      -- traceM "[2/3 checksynth]"
      return $ CAnd c c1

-- Selfificaiton
self :: Variable -> Type -> Type
self x (TRBase b (RKnown p)) = TRBase b (RKnown (PAnd p (PInterpOp Equal (PVar binder) (PVar x))))
self _ t = t

-- Templating

-- Generate fresh templates for the program
template :: Context -> [Variable] -> Term -> Gen Term
template p ctx (TConst k) = return (TConst k)
template p ctx (TVar v) = return (TVar v)
template p ctx (TLet v t1 t2) = do
  t1' <- template p ctx t1
  t2' <- template p (v : ctx) t2
  return $ TLet v t1' t2'
template p ctx (TLam v t) = do
  t' <- template p (v : ctx) t
  return $ TLam v t'
template p ctx (TApp t v) = do
  t' <- template p ctx t
  return $ TApp t' v
template p ctx (TAnn t ty) = do
  ty' <- fresh p ty
  t' <- template p ctx t
  return $ TAnn t' ty'
template p ctx (TCond v tt tf) = do
  tt' <- template p ctx tt
  tf' <- template p ctx tf
  return $ TCond v tt' tf'
template p ctx (TRec _ _ _ _) = do
  error "letrec is unsupported"
template p ctx (TTAbs v k t) = do
  error "ttabs is unsupported"
template p ctx (TTApp _ _) = do
  error "ttappis unsupported"

fresh :: Context -> Type -> Gen Type
fresh g (TRBase b Hole) = do
  v <- gensym
  k <- gensym
  let freshKappa = HornVariable k b (bToList $ getRng (g ^. terms))
  return $ TRBase b (RKnown (PHornApp freshKappa (bToList $ getDom (g ^. terms))))
fresh _ r@(TRBase _ (RKnown _)) = return r
fresh g (TDepFn x s t) = do
  s' <- fresh g s
  t' <- fresh (terms %~ tblSet x s' $ g) t
  return $ TDepFn x s' t'

-- Remove some tautologies from the output (closer matches the paper)
cleanupConstraint :: Constraint -> Constraint
cleanupConstraint c = case clean c of
  Nothing -> CPred (PBool True)
  Just c -> c
  where
    clean :: Constraint -> Maybe Constraint
    clean (CPred (PBool True)) = Nothing
    clean (CFun _ _ _ (CPred (PBool True))) = Nothing
    clean (CAnd c0 c1) =
      case (c01, c11) of
        (Nothing, Nothing) -> Nothing
        (Just c, Nothing) -> Just c
        (Nothing, Just c) -> Just c
        (Just c02, Just c03) -> Just $ CAnd c02 c03
      where
        c01 = clean c0
        c11 = clean c1
    clean (CFun v b p c) =
      clean c >>= Just . CFun v b p
    clean c = Just c

------ Typechecking a program

-- Typecheck all bodies in a program
tyckProgram :: Program -> Table FnName Constraint
tyckProgram p = foldl (\tsf fn -> tblSet fn (tyckF fn) tsf) (emptyTable Nothing) bods
  where
    -- For now, no type variables ;)
    ctxTy = foldl (\csf fn -> tblSet fn (getTbl (p ^. decls) fn) csf) (emptyTable Nothing) (p ^. (decls . dom))
    gamma = Context ctxTy (emptyTable Nothing)
    bods = p ^. (bodies . dom)
    tyckF fn = evalState (check gamma (getTbl (p ^. bodies) fn) (getTbl (p ^. decls) fn)) defaultState

-- Typecheck all bodies in a program
templateProgram :: Program -> Program
templateProgram p = foldl (\tsf fn -> decls %~ tblSet fn (tmplT fn) $ tsf) p dcs
  where
    -- For now, no type variables ;)
    ctxTy = foldl (\csf fn -> tblSet fn (getTbl (p ^. decls) fn) csf) (emptyTable Nothing) (p ^. (decls . dom))
    gamma = Context ctxTy (emptyTable Nothing)
    bods = p ^. (bodies . dom)
    dcs = p ^. (decls . dom)
    tmplF fn = evalState (template gamma [] (getTbl (p ^. bodies) fn)) defaultState
    tmplT fn = evalState (fresh gamma (getTbl (p ^. decls) fn)) defaultState
    bodiesTemplated = foldl (\tsf fn -> bodies %~ tblSet fn (tmplF fn) $ tsf) p bods

------ Tests

testCheck :: Context -> Term -> Type -> Constraint
testCheck gamma0 inc t0 = cleanupConstraint (evalState (check gamma0 inc t0) defaultState)

testSynth :: Context -> Term -> (Constraint, Type)
testSynth gamma0 t0 = let (cs, ty) = evalState (synth gamma0 t0) defaultState in (cleanupConstraint cs, ty)

setupContext :: [(Variable, Type)] -> [(TypeVariable, Kind)] -> Context
setupContext vBs aBs = g2
  where
    g0 = Context (emptyTable Nothing) (emptyTable Nothing)
    g1 = foldl (\g (v, t) -> terms %~ tblSet v t $ g) g0 vBs
    g2 = foldl (\g (v, t) -> types %~ tblSet v t $ g) g1 aBs

subTest :: Gen Constraint
subTest = sub example36Sub example36Sup
  where
    example36Sub :: Type
    example36Sub =
      TDepFn
        "x"
        (base BInt)
        (TRBase BInt (RKnown (PInterpOp Equal (PVar binder) (PInterpOp Add (PVar "x") (PInt 1)))))

    example36Sup :: Type
    example36Sup =
      TDepFn
        "x"
        (TRBase BInt (RKnown (PInterpOp Leq (PInt 0) (PVar "x"))))
        (TRBase BInt (RKnown (PInterpOp Leq (PInt 0) (PVar binder))))

nat :: Type
nat = TRBase BInt (RKnown (PInterpOp Leq (PInt 0) (PVar binder)))

vcTest1 :: Constraint
vcTest1 = testCheck gamma0 inc t0
  where
    gamma0 =
      Context
        (tblSet "x" nat (tblSet "one" (TRBase BInt (RKnown (PInterpOp Equal (PVar binder) (PInt 1)))) (emptyTable Nothing)))
        (emptyTable Nothing)
    t0 = TRBase BInt (RKnown (PInterpOp Lt (PVar "x") (PVar binder)))
    inc = TApp (TApp (TConst (CNOp Add)) "x") "one"

vcTest2 :: Constraint
vcTest2 = testCheck gamma1 term1 t0
  where
    inc = TApp (TApp (TConst (CNOp Add)) "x") "one"
    t0 = TRBase BInt (RKnown (PInterpOp Lt (PVar "x") (PVar binder)))
    gamma1 = Context (tblSet "x" nat (emptyTable Nothing)) (emptyTable Nothing)
    term1 = TLet "one" (TConst (CNInt 1)) inc

vcTest3 :: Constraint
vcTest3 = testCheck (Context (emptyTable Nothing) (emptyTable Nothing)) term3 typ3
  where
    inc = TApp (TApp (TConst (CNOp Add)) "x") "one"
    term1 = TLet "one" (TConst (CNInt 1)) inc
    term3 = TLam "x" term1
    t0 = TRBase BInt (RKnown (PInterpOp Lt (PVar "x") (PVar binder)))
    typ3 = TDepFn "x" nat t0

-- Example from 4.3.1
notTest :: Constraint
notTest = testCheck tbl term typ
  where
    tbl = Context (tblSet "x" (base BBool) (emptyTable Nothing)) (emptyTable Nothing)
    term = TCond "x" (TConst (CNBool True)) (TConst (CNBool False))
    typ = TRBase BBool $ RKnown (PInterpOp Equal (PVar binder) (PNeg (PVar "x")))

-- Another example from 4.3.1

sumTest :: Constraint
sumTest = testCheck tbl term typ
  where
    ts =
      TRBase BInt $
        RKnown $
          PAnd
            (PInterpOp Leq (PInt 0) (PVar binder))
            (PInterpOp Leq (PVar "n") (PVar binder))
    tbl =
      Context
        ( tblSet "n" (base BInt) $
            tblSet "sum" (TDepFn "n" (base BInt) ts) $
              emptyTable Nothing
        )
        (emptyTable Nothing)
    typ = ts
    term =
      TLet "c" todo $
        TCond
          "c"
          (TConst (CNInt 0))
          ( TLet "n1" todo $
              TLet "n2" todo todo
          )

clientTest = testSynth g e0
  where
    -- testSynth g (TVar "max")
    -- testCheck tbl client typ

    g =
      setupContext
        [ ("v_zero", prim (CNInt 0)),
          ("v_five", prim (CNInt 5)),
          ("v_one", prim (CNInt 1)),
          ("max", TForall "alpha" BaseKind (TDepFn "bv0" (base (BTVar "alpha")) (TDepFn "bv1" (base (BTVar "alpha")) (base (BTVar "alpha"))))),
          ("add", TDepFn "x" (base BInt) (TRBase BInt (RKnown (PInterpOp Equal (PVar binder) (PInterpOp Add (PVar "x") (PInt 1))))))
        ]
        []
    client =
      TLet "r" (TApp (TApp (TVar "max") "v_zero") "v_five") $
        TApp (TApp (TVar "add") "r") "v_one"
    e0 = TTApp (TVar "max") (TRBase BInt Hole)
    typ = todo
