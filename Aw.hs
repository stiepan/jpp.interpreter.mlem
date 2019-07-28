module Aw where

-- This module is heavily inspired by Algorithm W Step by Step paper so does some definitions
-- especially the idea of having class Types resulted in almost literally identical code.

import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.Trans.State
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Except
import Control.Monad.Trans.Class 
import Data.Functor.Identity

import AbsMlemBitter

type TVName = String

type VName = String

data Type 
    = TInt
    | TBool
    | TVar TVName
    | TFun Type Type
    | TList Type
    deriving (Eq, Ord, Show, Read)

-- generalized type where [TVName] are universally quantified
data GType = GType [TVName] Type 
    deriving (Eq, Ord, Show, Read)

-- finite mapping from type variables names to types 
type Subst = Map.Map TVName Type 

-- Environment of variables called gamma in HM type rules. 
-- Couldn't use merely type for synonym due to class instantiation
newtype Gamma = Gamma {tenv :: Map.Map VName GType}
    deriving (Eq, Ord, Show, Read)

type Ti a = ReaderT Gamma (StateT Integer (ExceptT String Identity)) a

throw = lift.lift.throwE

class Types a where
    -- free type variables within object
    ftv :: a -> Set.Set TVName
    -- applies substitution to the given object
    apply :: Subst -> a -> a 

instance Types Type where
    ftv (TVar v) = Set.singleton v
    ftv TInt = Set.empty
    ftv TBool = Set.empty
    ftv (TFun t1 t2) = ftv t1 `Set.union` ftv t2
    ftv (TList t) = ftv t

    apply s tv@(TVar v) = case Map.lookup v s of
                               Just t -> t
                               _ -> tv
    apply s (TFun t1 t2) = TFun (apply s t1) (apply s t2)
    apply s (TList t) = TList (apply s t)
    apply _ t = t

instance Types GType where
    ftv (GType vs t) = ftv t `Set.difference` (Set.fromList vs)

    apply s (GType vs t) = GType vs (apply noQuantTVars t)
        where noQuantTVars = foldr Map.delete s vs

instance Types a => Types [a] where
    ftv = foldr ((Set.union).ftv) Set.empty
    
    apply s = map (apply s)

instance Types Gamma where
    ftv env = ftv (Map.elems (tenv env))
    
    apply s env = Gamma (Map.map (apply s) (tenv env))

runTi mti = runIdentity (runExceptT (runStateT (runReaderT mti gamma0) state0))
    where
    gamma0 = Gamma (Map.fromList (map (\(s, t) -> (s, to_gtype t)) [
        ("_||", TFun TBool (TFun TBool TBool)),
        ("_&&", TFun TBool (TFun TBool TBool)),
        ("_!", TFun TBool TBool),
        ("_+", TFun TInt (TFun TInt TInt)),
        ("_-", TFun TInt (TFun TInt TInt)),
        ("_--", TFun TInt TInt),
        ("_*", TFun TInt (TFun TInt TInt)),
        ("_/", TFun TInt (TFun TInt TInt)),
        ("_%", TFun TInt (TFun TInt TInt)),
        ("_<", TFun TInt (TFun TInt TBool)),
        ("_<=", TFun TInt (TFun TInt TBool)),
        ("_>", TFun TInt (TFun TInt TBool)),
        ("_>=", TFun TInt (TFun TInt TBool)),
        ("_==", TFun TInt (TFun TInt TBool)),
        ("_!=", TFun TInt (TFun TInt TBool))]))
    state0 = 0

check :: MExpr -> Either String Type
check exp = 
    case runTi (ti exp) of
        Right ((_, t), _) -> Right t
        Left s -> Left s

ti :: MExpr -> Ti (Subst, Type)

ti (MLit constr) = constrType constr 
    where
    constrType (MListLitE) = do
        vt <- newTypeVar
        return (subst0, TList vt)
    constrType (MListLitC e1 e2) = do
        env <- ask
        (s1, t1) <- ti e1
        (s2, t2) <- local (const (apply s1 env)) (ti e2)
        s <- unify (TList (apply s2 t1)) t2
        return (s `compose` s2 `compose` s1, apply s t2)
    constrType (MVarLit (MIdent pos v)) = do
        Gamma env <- ask
        case Map.lookup v env of
            Nothing -> throw ("Undeclarated variable " ++ v ++ " at " ++ (show pos))
            Just gt -> do
                t <- specialized gt
                return (subst0, t)
    constrType (constr) = return (subst0, t)
        where
        t = case constr of
                MIntLit _ -> TInt
                MBoolLitT -> TBool
                MBoolLitF -> TBool

ti e@(MAbs (MIdent pos v) exp) = do
    Gamma env <- ask
    vt <- newTypeVar
    let nenv = Gamma (Map.insert v (to_gtype vt) env)
    (s, t) <- local (const nenv) (ti exp)
    return (s, TFun (apply s vt) t)

ti (MApp e1 e2) = do
    env <- ask
    (s1, t1) <- ti e1
    (s2, t2) <- local (const (apply s1 env)) (ti e2)
    nt <- newTypeVar
    s <- unify (apply s2 t1) (TFun t2 nt)
    return (s `compose` s2 `compose` s1, apply s nt)

ti (MLet vs exp) = do
    Gamma env <- ask
    freshVars <- mapM (const newTypeVar) vs
    let gFreshVars = map to_gtype freshVars
        tvns = map (\(MAssig (MIdent _ v) _) -> v) vs
        eenv = Map.fromList (zip tvns gFreshVars)
        nenv = Gamma (eenv `Map.union` env)
    (s, Gamma fenv) <- local (const nenv) (foldDecls vs)
    let genv = foldr (\v aenv -> Map.update (\t -> Just (generalized (Gamma aenv) (to_type t))) v aenv) fenv tvns
    (sin, t) <- local (const (Gamma genv)) (ti exp)
    return (sin `compose` s, t)
    where
    foldDecls :: [MAssig] -> Ti (Subst, Gamma)
    foldDecls [] = do
        fenv <- ask
        return (subst0, fenv)
    foldDecls (e@(MAssig (MIdent pos v) expv):t) = do
        (s, g@(Gamma fenv)) <- foldDecls t
        (s', tv) <- local (const g) (ti expv)
        let vtype = apply s' (fenv Map.! v)
        us <- unify (to_type vtype) tv
        let fs = us `compose` s'
        return (fs `compose` s, apply fs (Gamma fenv))

ti (MMatch e rs) = do
    (se, te) <- ti e
    (fse, fst) <- unifyPats se te rs
    tres <- newTypeVar
    tcheck (fse `compose` se) tres fst rs
    where
    fv :: MConstr -> Ti (Set.Set String)
    fv (MVarLit (MIdent _ v)) = return (Set.singleton v)
    fv (MListLitC e1 e2) =
        case (e1, e2) of
             (MLit c1, MLit c2) -> do
                fv1 <- fv c1
                fv2 <- fv c2
                return (fv1 `Set.union` fv2)
             _ -> throw "Incorrect expression in the pattern"
    fv _ = return Set.empty
    withPatVars c = do 
        fvs <- fv c
        let fvsl = Set.toList fvs
        fvts <- mapM (const newTypeVar) fvsl
        Gamma lenv <- ask
        let nlenv = foldr (\(v, vt) env -> Map.insert v (to_gtype vt) env) lenv (zip fvsl fvts)
        return (Gamma nlenv)
    unifyPats se te ((MRule c _):rs) = do 
        nlenv <- withPatVars c
        (sp, tp) <- local (const nlenv) (ti (MLit c))
        s <- unify (apply sp te) tp
        unifyPats (s `compose` sp `compose` se) (apply s te) rs
    unifyPats se te [] = return (se, te)
    tcheck sacc tres te ((MRule c exp):rs) = do 
        nlenv <- withPatVars c
        (sp, tp) <- local (const nlenv) (ti (MLit c))
        s <- unify (apply sp te) tp
        (sexp, texp) <- local (const (apply sacc nlenv)) (ti exp)
        sres <- unify (apply sexp tres) texp
        let nsacc = sres `compose` sexp
        tcheck nsacc (apply nsacc tres) (apply nsacc te) rs
    tcheck sacc tres _ [] = return (sacc, tres)

unify :: Type -> Type -> Ti Subst

unify (TFun lt1 lt2) (TFun rt1 rt2) = do
    s1 <- unify lt1 rt1
    s2 <- unify (apply s1 lt2) (apply s1 rt2)
    return (s2 `compose` s1)
unify (TList t1) (TList t2) = unify t1 t2
unify (TVar v) t = unifyVar v t
unify t (TVar v) = unifyVar v t
unify t1 t2
    | t1 == t2 = return subst0
    | otherwise = throw ((show t1) ++ " and " ++ (show t2) ++ " don't unify")

unifyVar :: TVName -> Type -> Ti Subst
unifyVar v t
    | TVar v == t = return subst0
    | v `Set.member` (ftv t) = throw ("Cannot construct recurssive type " ++ v ++ " = " ++ (show t))
    | otherwise = return (Map.singleton v t)

subst0 :: Subst
subst0 = Map.empty

compose :: Subst -> Subst -> Subst
compose s1 s2 = Map.map (apply s1) s2 `Map.union` s1

newTypeVar :: Ti Type
newTypeVar = do
    n <- lift get
    lift (put (n + 1))
    return (TVar ("x_" ++ (show n)))

specialized :: GType -> Ti Type
specialized (GType vs t) = do 
    freshVars <- mapM (const newTypeVar) vs
    return (apply (Map.fromList (zip vs freshVars)) t)

generalized :: Gamma -> Type -> GType
generalized env t = do
    GType (Set.toList ((ftv t) `Set.difference` (ftv env))) t

to_gtype :: Type -> GType 
to_gtype t = GType [] t

to_type :: GType -> Type 
to_type (GType _ t) = t
