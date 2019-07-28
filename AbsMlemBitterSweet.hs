module AbsMlemBitterSweet where

-- Translates syntactic sugar to abs grammar that will be actually type checked and run

import AbsMlem
import AbsMlemBitter

t :: Expr -> MExpr
t (EOr e1 (Or pn) e2) = to_app pn [e1, e2]
t (EAnd e1 (And pn) e2) = to_app pn [e1, e2]
t (ENot (Not pn) e) = to_app pn [e]
t (ERel e1 op e2) = to_app pn [e1, e2]
    where pn = case op of
                  LTH (LTHT pn)-> pn
                  LE (LET pn) -> pn
                  GTH (GTHT pn) -> pn
                  GE (GET pn) -> pn
                  EQU (EQUT pn) -> pn
                  NE (NET pn) -> pn
t (EAdd e1 op e2) = to_app fname [e1, e2]
    where fname = case op of
                      Plus (PlusT pn) -> pn
                      Minus (MinusT pn) -> pn
t (EMul e1 op e2) = to_app fname [e1, e2]
    where fname = case op of
                      Times (TimesT pn) -> pn
                      Div (DivT pn) -> pn
                      Mod (ModT pn) -> pn
t (ENeg (MinusT (pos, _)) e) = to_app (pos, "--") [e]

t (EIf e1 e2 e3) = MMatch (t e1) [MRule MBoolLitT (t e2), MRule MBoolLitF (t e3)]

t e@(EAbs _ _) = uncarry e 

t (ELet asgs e) = MLet (map to_assig asgs) (t e)
    where
    to_assig (Assig (EIdent (pos, v)) e) = MAssig (MIdent pos v) (t e)
    to_assig (AssigF (EIdent (pos, v)) args e) = MAssig (MIdent pos v) (uncarry (EAbs args e))

t (EApp e1 e2) = MApp (t e1) (t e2)

t (EMatch e rs) = MMatch (t e) (map to_mrule rs)
    where
    to_mrule (ERule c e) = MRule (to_mconstr c) (t e)

t (ELit c) = MLit (to_mconstr c)

uncarry (EAbs as e) = foldr (\(EArg (EIdent (pos, v))) exp -> MAbs (MIdent pos v) exp) (t e) as

to_mconstr (VarLit (EIdent (p, v))) = MVarLit (MIdent p v)
to_mconstr (IntLit n) = MIntLit n
to_mconstr (BoolLitT) = MBoolLitT
to_mconstr (BoolLitF) = MBoolLitF
to_mconstr (ListLitE) = MListLitE
to_mconstr (ListLitC e1 e2) = MListLitC (t e1) (t e2)
to_mconstr (ListLitEn es) = foldr (\e a-> MListLitC e (MLit a)) MListLitE (map t es)

to_app pos_name (e:es) = foldl (MApp) (MApp (MLit (MVarLit (MIdent pos ("_" ++ name)))) (t e)) (map t es)
    where (pos, name) = pos_name

