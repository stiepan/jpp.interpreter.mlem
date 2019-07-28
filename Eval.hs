module Eval
where

import AbsMlemBitter
import qualified Data.Map as Map
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Except
import Control.Monad.Trans.Class 
import Data.Functor.Identity

type Env = Map.Map String Value

type Eval a = ReaderT Env (ExceptT String Identity) a

data Value
    = VInt Integer
    | VBool Bool
    | VList [Value]
    | VClos MExpr Env

instance Show Value where
    show (VInt n) = show n
    show (VBool b) = show b
    show (VList l) = (show l)
    show (VClos _ _) = (show "fun")

runEval ev env = runIdentity (runExceptT (runReaderT ev env)) 

throw = lift.throwE
  
idnt s = MIdent (0, 0) s
lamb s e = MAbs (idnt s) e
var s = MLit (MVarLit (idnt s))
binary c f = VClos (lamb "x" (lamb "y" (MBuiltIn (c (var "x") (var "y") f)))) Map.empty
unary c f = VClos (lamb "y" (MBuiltIn (c (var "y") f))) Map.empty
 
eval exp = runEval (evaluate exp) env0 
    where 
    env0 = Map.fromList [
        ("_||", binary MLogic (||)),
        ("_&&", binary MLogic (||)),
        ("_!", unary MNot (not)),
        ("_--", unary MNeg (\x -> -x)),
        ("_+", binary MArt (+)),
        ("_-",  binary MArt (-)),
        ("_*", binary MArt (*)),
        ("_/", binary MArt (div)),
        ("_%", binary MArt (mod)),
        ("_<", binary MRel (<)),
        ("_<=", binary MRel (<=)),
        ("_>", binary MRel (>)),
        ("_>=", binary MRel (>=)),
        ("_==", binary MRel (==)),
        ("_!=", binary MRel (/=))]
    
evaluate :: MExpr -> Eval Value

evaluate (MBuiltIn e) = 
    case e of
        (MLogic e1 e2 f) -> do
            (VBool v1) <- evaluate e1
            (VBool v2) <- evaluate e2
            return (VBool (f v1 v2))
        (MRel e1 e2 f) -> do
            (VInt v1) <- evaluate e1
            (VInt v2) <- evaluate e2
            return (VBool (f v1 v2))
        (MArt e1 e2 f) -> do
            (VInt v1) <- evaluate e1
            (VInt v2) <- evaluate e2
            return (VInt (f v1 v2))
        (MNot e f) -> do
            (VBool v) <- evaluate e
            return (VBool (f v))
        (MNeg e f) -> do
            (VInt v) <- evaluate e
            return (VInt (f v))

evaluate (MLit c) =
    case c of
        (MVarLit (MIdent _ v)) -> do
            env <- ask
            return (env Map.! v)
        (MIntLit n) -> return (VInt n)
        MBoolLitT -> return (VBool True)
        MBoolLitF -> return (VBool False)
        MListLitE -> return (VList [])
        (MListLitC h t) -> do
            lh <- evaluate h
            (VList lt) <- evaluate t
            return (VList (lh:lt))

evaluate (MLet as exp) = do 
    env <- ask
    let genv = do
        upd <- mapM (\(MAssig (MIdent _ v) vexp) -> 
                    (local (const (let (Right nenv) = (runEval genv env) in nenv))
                    (evaluate vexp)) >>= (\val -> return (v, val))
                    ) as
        return ((Map.fromList upd) `Map.union` env)
    nenv <- genv
    local (const nenv) (evaluate exp)

evaluate (MMatch e rs) = do 
    ve <- evaluate e
    (subst, re) <- matchFirst ve rs
    env <- ask
    local (const (subst `Map.union` env)) (evaluate re)
    where
    matchFirst :: Value -> [MRule] -> Eval (Env, MExpr)
    matchFirst ve [] =
        throw ("Pattern matching failure at " ++ (show e))
    matchFirst ve ((MRule c e):rs) = do
        case (unify ve c) of
            Just subst -> return (subst, e)
            Nothing -> matchFirst ve rs
    unify ve (MVarLit (MIdent _ v)) = Just (Map.singleton v ve)
    unify (VBool b) (MBoolLitT) 
        | b = Just Map.empty
        | otherwise = Nothing
    unify (VBool b) (MBoolLitF)
        | not b = Just Map.empty
        | otherwise = Nothing
    unify (VInt n) (MIntLit m)
        | m == n = Just Map.empty
        | otherwise = Nothing
    unify (VList []) (MListLitE) = Just Map.empty
    unify (VList (h:t)) (MListLitC (MLit c1) (MLit c2)) =
        case (unify h c1, unify (VList t) c2) of
             (Just s1, Just s2) -> Just (s2 `Map.union` s1)
             _ -> Nothing
    unify _ _ = Nothing

evaluate e@(MAbs _ _) = do
    env <- ask
    return (VClos e env)

evaluate (MApp e1 e2) = do
    v1 <- evaluate e1
    v2 <- evaluate e2
    apply v1 v2

apply (VClos (MAbs (MIdent _ v) lbody) env) v2 = 
    local (const (Map.insert v v2 env)) (evaluate lbody)

