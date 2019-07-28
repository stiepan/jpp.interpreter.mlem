module AbsMlemBitter where

-- Abstract grammar with no syntactic sugar

data MExpr 
    = MAbs MIdent MExpr
    | MLet [MAssig] MExpr
    | MApp MExpr MExpr
    | MMatch MExpr [MRule]
    | MLit MConstr
    | MBuiltIn Magic -- these are not present after parsing 
    -- they are added after type checking just before evaluation
  deriving Show

data Magic 
    = MLogic MExpr MExpr (Bool -> Bool -> Bool)
    | MRel MExpr MExpr (Integer -> Integer -> Bool)
    | MArt MExpr MExpr (Integer -> Integer -> Integer)
    | MNot MExpr (Bool -> Bool)
    | MNeg MExpr (Integer -> Integer)

instance Show Magic where
    show _ = "built-in"
 
data MRule = MRule MConstr MExpr
  deriving Show

data MAssig = MAssig MIdent MExpr
  deriving Show

data MConstr
    = MVarLit MIdent
    | MIntLit Integer
    | MBoolLitT
    | MBoolLitF
    | MListLitE
    | MListLitC MExpr MExpr
  deriving Show

data MIdent = MIdent (Int, Int) String
  deriving Show
