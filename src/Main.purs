module Main where

import Prelude

import Effect (Effect)
import Effect.Console (log)
import Effect.Class (class MonadEffect)

import Data.Maybe (Maybe(..), fromMaybe)
import Data.List
  ( List(..), (:), (!!), span, singleton, find, zip, fromFoldable, drop
  , length, toUnfoldable, head, tail
  , manyRec, someRec)
import Data.Either (Either(..))
import Data.Map as Map
import Data.Array (updateAt)
import Data.Array as A
import Data.Char (toCharCode, fromCharCode)
import Data.Int.Bits as IB
import Data.String (split, joinWith)
import Data.String.Pattern (Pattern(..))
import Data.String.CodeUnits (fromCharArray)
import Data.String.CodeUnits as SCU
import Data.Tuple (Tuple(..), lookup, fst, snd)
-- import Data.Unfoldable
import Data.Foldable (fold, for_)
import Data.Traversable (for, traverse)

import Control.Alt ((<|>))
import Control.Monad.State (State, runState, evalState)
import Control.Monad.RWS (RWS, tell, ask, get, gets, put, modify_, runRWS, execRWS, RWSResult(..))
import Control.Monad.Cont (ContT, callCC, runContT)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Trans.Class (lift)

import Text.Parsing.Parser (ParserT, runParserT, Parser, runParser, ParseState(..))
import Text.Parsing.Parser.String as PS
import Text.Parsing.Parser.Combinators as PC
import Text.Parsing.Parser.Token as PT
import Text.Parsing.Parser.Expr as PE

import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Core as HC
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.Aff as HA
import Halogen.VDom.Driver (runUI)
import Web.HTML.HTMLTextAreaElement as HTextArea
import Web.HTML.HTMLSelectElement as HSelect

data Val =
    VVoid
  | VInt Int
  | VFloat Number
  | VUndef
  | VArray (Array Val)
  | VRef LVal

instance showVal :: Show Val where
  show VVoid = "void"
  show (VInt x) = show x
  show VUndef = fromMaybe "#undefined" $ SCU.singleton <$> fromCharCode 0x22A5
  show (VArray x) = show x
  show (VRef lv) = show lv
  show _ = "todo"

data LVal =
   LVAtom Int String
 | LVAryEl Int String Int

instance showLVal :: Show LVal where
  show (LVAtom frid id) = "#ref[(" <> show frid <> ") " <> id <> "]"
  show (LVAryEl frid id ix) = "#ref[(" <> show frid <> ") " <> id <> "[" <> show ix <> "]]"

data PrimopBin =
    PoAdd | PoSub | PoMul | PoDiv | PoMod
  | PoEq | PoNeq | PoLT | PoLTE | PoGT | PoGTE
  | PoShL | PoShR | PoBitand | PoBitor | PoBitxor
  | PoAnd | PoOr

data PrimopUn = PoNeg | PoNot | PoBitnot

primopBin :: PrimopBin -> Int -> Int -> Int
primopBin op = case op of
  PoAdd -> (+)
  PoSub -> (-)
  PoMul -> (*)
  PoDiv -> (/)
  PoMod -> mod
  PoEq -> \a b -> if a == b then 1 else 0
  PoNeq -> \a b -> if a /= b then 1 else 0
  PoLT -> \a b -> if a < b then 1 else 0
  PoLTE -> \a b -> if a <= b then 1 else 0
  PoGT -> \a b -> if a > b then 1 else 0
  PoGTE -> \a b -> if a >= b then 1 else 0
  PoShL -> IB.shl
  PoShR -> IB.shr
  PoBitand -> IB.and
  PoBitor -> IB.or
  PoBitxor -> IB.xor
  PoAnd -> \a b -> if a /= 0 && b /= 0 then 1 else 0
  PoOr -> \a b -> if a == 0 && b == 0 then 0 else 1

primopUn :: PrimopUn -> Int -> Int
primopUn op = case op of
  PoNeg -> \a -> -a
  PoNot -> \a -> if a == 0 then 1 else 0
  PoBitnot -> \a -> IB.complement a

data Expr =
    EId String
  | EConst Val
  | ESubscr Expr Expr
  | EAs Expr Expr
  | ECall String (List Expr)
  | EBinop PrimopBin Expr Expr
  | EUnop PrimopUn Expr
  | ETernop Expr Expr Expr
  | EIncr EIPrePost EIIncDec Expr
  | EAddr Expr

data EIPrePost = EIPre | EIPost
data EIIncDec = EIInc | EIDec

instance showExpr :: Show Expr where
  show (EId id) = show id
  show (EConst v) = show v
  show _ = "todo"

type Frame =
  { name :: String
  , env :: Map.Map String Val
  , frid :: Int
  }

data Config = Config
  { frs :: List Frame
  , stdout :: String
  , stdin :: String
  }

ceval :: Expr -> RunM Val
ceval e = case e of
  EId id -> leval e >>= readlval
  EConst k -> pure k
  ESubscr ar ix -> leval e >>= readlval
  EAs loc val -> do
    lv <- leval loc
    v <- ceval val
    writelval lv v
    pure v
  ECall id args -> runm (ProgCall id args) pure pure pure
  EBinop op a b -> do
    av <- ceval a
    bv <- ceval b
    let
      r = case av of
        VInt avi -> case bv of
          VInt bvi -> VInt $ (primopBin op) avi bvi
          _ -> VVoid
        _ -> VVoid
    pure r
  EUnop op a -> do
    av <- ceval a
    pure $ case av of
      VInt avi -> VInt $ primopUn op avi
      _ -> VVoid
  ETernop _ _ _ -> pure VVoid
  EIncr pp inc expr -> do
    let
      adder = case inc of
        EIInc -> 1
        EIDec -> -1
      op = EAs expr $ EBinop PoAdd expr (EConst $ VInt adder)
    lv <- leval expr
    case pp of
      EIPre -> ceval op *> readlval lv
      EIPost -> readlval lv <* ceval op
  EAddr a -> VRef <$> leval a

leval :: Expr -> RunM LVal
leval e = case e of
  EId id -> do
    Config c <- gets _.config
    case head c.frs of
      Just fr -> pure $ LVAtom fr.frid id
      Nothing -> throwError "unreachable: no frames existing"
  ESubscr ar ix -> ceval ar >>= case _ of
    VRef (LVAtom frid id) -> ceval ix >>= case _ of
      VInt ixvi -> pure $ LVAryEl frid id ixvi
      _ -> throwError "index must be int in subscript expression"
    _ -> throwError "name must refer to array in subscript expression"
  _ -> throwError "leval not defined"

frameput :: Int -> Frame -> RunM Unit
frameput frid fr' = do
  Config c <- gets _.config
  let { init: frin, rest: frrs } = span (\fr -> fr.frid /= frid) c.frs
  case frrs of
    Nil -> throwError "frame not found"
    fr : below -> do
      let y = Config $ c{ frs = frin <> singleton fr' <> below }
      trace y
      modify_ $ _{ config = y }

frameget :: Int -> RunM Frame
frameget frid = do
  Config c <- gets _.config
  case flip find c.frs (\fr -> fr.frid == frid) of
    Just x -> pure x
    Nothing -> throwError "frame not found"

framegettop :: RunM Frame
framegettop = do
  Config c <- gets _.config
  case head c.frs of
    Just fr -> pure fr
    Nothing -> throwError "top frame must exist"

readlval :: LVal -> RunM Val
readlval lv = case lv of
  LVAtom frid id -> do
    fr <- frameget frid
    case Map.lookup id fr.env of
      Just (VArray _) -> pure $ VRef lv
      Just v -> pure v
      Nothing -> throwError "var name not found in frame"
  LVAryEl frid id ix -> do
    fr <- frameget frid
    case Map.lookup id fr.env of
      Just (VArray ar) -> case ar A.!! ix of
        Just v -> pure v
        Nothing -> throwError "index out of bounds"
      Just _ -> throwError "can't index non array value"
      Nothing -> throwError "var name not found in frame"

writelval :: LVal -> Val -> RunM Unit
writelval lv v = case lv of
  LVAtom frid id -> do
    fr <- frameget frid
    let env' = Map.insert id v fr.env
    frameput frid $ fr { env = env' }
  LVAryEl frid id ix -> do
    fr <- frameget frid
    case Map.lookup id fr.env of
      Just (VArray ary) -> do
        case VArray <$> updateAt ix v ary of
          Just ary' -> do
            let env' = Map.insert id ary' fr.env
            frameput frid $ fr { env = env' }
          _ -> throwError "write array index out of bounds"
      _ -> throwError "write array element invalid array"

data ProgF =
    ProgExpr Expr
  | ProgCall String (List Expr)
  | ProgRet Expr
  | ProgAllocVar String
  | ProgAllocAry String Expr
  | ProgIOW
  | ProgIOR
  | ProgSeq (List ProgF)
  | ProgWhile Expr ProgF
  | ProgFor Expr Expr Expr ProgF
  | ProgIf Expr ProgF
  | ProgIfElse Expr ProgF ProgF
  | ProgSwitch Expr (List (Tuple (Maybe Val) ProgF)) -- maybe used to encode default
  | ProgBreak
  | ProgContinue

data Argdef =
    Argdef (List String)
  | Argvar (List String)

type Prog = List { fname :: String, argns :: Argdef, code :: ProgF }

stdlib :: Prog
stdlib = fromFoldable
  [ { fname: "printf", argns: Argvar $ fromFoldable ["format"], code: stdlib_printf }
  , { fname: "scanf", argns: Argvar $ fromFoldable ["format"], code: stdlib_scanf }
  ]
  where
  stdlib_printf = ProgIOW
  stdlib_scanf = ProgIOR

type PreprocDef = Map.Map String String

preprocessor :: String -> String
preprocessor inp =
  let m = traverse go (split (Pattern "\n") inp)
  in joinWith "\n" $ evalState m Map.empty
  where
  go :: String -> State PreprocDef String
  go row = do
    s <- get
    case runParser row (pp s) of
      Right a -> a
      Left _ -> pure ""

  pp :: PreprocDef -> Parser String (State PreprocDef String)
  pp s = PC.choice
    [ do
        PS.string "#define" *> PC.skipMany1 PT.space
        id <- ident
        PS.skipSpaces
        v <- PC.optionMaybe $ (fromCharArray <<< toUnfoldable) <$> manyRec PS.anyChar
        pure $ do
          modify_ $ Map.insert id $ fromMaybe "" v
          pure ""
    , PS.string "#" *> pure (pure "")
    , pure <$> fold <$> manyRec expand
    ]
    where
    expand = do
      PC.choice
        [ do
            id <- ident
            pure $ fromMaybe id $ Map.lookup id s
        , do
            _ <- PS.char '"'
            str <- fromCharArray <<< toUnfoldable <$> manyRec (PS.noneOf ['"'])
            _ <- PS.char '"'
            pure $ "\"" <> str <> "\""
        , SCU.singleton <$> PS.anyChar
        ]
    ident = do
      f <- PT.letter <|> PS.char '_'
      r <- manyRec PT.alphaNum
      pure $ fromCharArray [f] <> fromCharArray (toUnfoldable r)

type ParS = { fr :: Frame, nxid :: Int }
type ParP = ParserT String (State ParS)

parse :: String -> Maybe (Tuple Prog Config)
parse input = case runState (runParserT input prog)
    { fr: { name: "#static", env: Map.empty, frid: 0 }
    , nxid: 0 } of
  Tuple (Left _) _ -> Nothing
  Tuple (Right x) s -> Just $ Tuple x $ Config
    { frs: singleton s.fr, stdin: "", stdout: "" }
  where
    prog :: ParP Prog
    prog = someRec func

    ident :: ParP String
    ident = do
      f <- PT.letter <|> PS.char '_'
      r <- manyRec (PT.alphaNum <|> PS.char '_')
      PS.skipSpaces
      pure $ fromCharArray [f] <> fromCharArray (toUnfoldable r)

    tkc :: Char -> ParP Char
    tkc c = PS.char c <* PS.skipSpaces

    func :: ParP { fname :: String, argns :: Argdef, code :: ProgF }
    func = do
      _ <- PS.skipSpaces *> type_name *> PC.skipMany1 PT.space
      fname <- ident
      _ <- tkc '('
      args <- PC.sepBy (type_name *> PC.skipMany1 PT.space *> argdecl) (tkc ',')
      _ <- tkc ')'
      _ <- tkc '{'
      stmts <- manyRec stmt
      _ <- tkc '}'
      pure $ { fname: fname, argns: Argdef args, code: ProgSeq stmts }
      where
      argdecl = ident <* PC.optional (PS.string "[]")

    number :: ParP Int
    number = do
      xs <- map ((\x -> x-0x30) <<< toCharCode) <$> someRec PT.digit <* PS.skipSpaces
      pure $ conv xs 0
      where
      conv Nil n = n
      conv (x:xs) n = conv xs (10*n + x)

    expr :: ParP Expr
    expr = expr_tree -- <|> expr_base
      where
      expr_base :: ParP Expr
      expr_base = PC.choice
        [ EConst <<< VInt <$> number
        , do
            _ <- PS.char '"'
            cs <- manyRec $ PC.choice
              [ do
                  _ <- PS.char '\\'
                  c <- PS.anyChar
                  case c of
                    '"' -> pure c
                    'n' -> pure '\n'
                    '\\' -> pure '\\'
                    _ -> pure c
              , PS.noneOf ['"']
              ]
            _ <- tkc '"'
            { fr: stfr, nxid: stid } <- lift get
            let
              idname = "#s:" <> show stid
              ary = VArray $ map (VInt <<< toCharCode) $ toUnfoldable cs
              stfr' = stfr { env = Map.insert idname ary stfr.env }
            lift $ put { fr: stfr', nxid: (stid + 1) }
            pure $ EConst $ VRef $ LVAtom stfr.frid idname
        , PC.try $ do
            a <- ident
            _ <- tkc '['
            ix <- expr
            _ <- tkc ']'
            pure $ ESubscr (EId a) ix
        , PC.try $ do
            fn <- ident
            _ <- tkc '('
            args <- PC.sepBy expr $ tkc ','
            _ <- tkc ')'
            pure $ ECall fn args
        , EId <$> ident
        , do
            _ <- tkc '('
            e <- expr
            _ <- tkc ')'
            pure e
        ]

      expr_tree :: ParP Expr
      expr_tree = PE.buildExprParser
        [ [ PE.Prefix $ long "++" $> EIncr EIPre EIInc
          , PE.Prefix $ long "--" $> EIncr EIPre EIDec
          ]
        , [ PE.Postfix $ long "++" $> EIncr EIPost EIInc
          , PE.Postfix $ long "--" $> EIncr EIPost EIDec
          ]
        , [ PE.Prefix $ tkc '~' $> EUnop PoBitnot
          , PE.Prefix $ tkc '!' $> EUnop PoNot
          , PE.Prefix $ tkc '-' $> EUnop PoNeg
          , PE.Prefix $ (PC.lookAhead (PS.string "&&") <|> (tkc '&' $> "")) $> EAddr
          ]
        , [ PE.Infix (tkc '*' $> EBinop PoMul) PE.AssocLeft
          , PE.Infix (tkc '/' $> EBinop PoDiv) PE.AssocLeft
          , PE.Infix (tkc '%' $> EBinop PoMod) PE.AssocLeft
          ]
        , [ PE.Infix (tkc '+' $> EBinop PoAdd) PE.AssocLeft
          , PE.Infix (tkc '-' $> EBinop PoSub) PE.AssocLeft
          ]
        , [ PE.Infix (long "<<" $> EBinop PoShL) PE.AssocLeft
          , PE.Infix (long ">>" $> EBinop PoShR) PE.AssocLeft
          ]
        , [ PE.Infix (long ">=" $> EBinop PoGTE) PE.AssocLeft
          , PE.Infix (long "<=" $> EBinop PoLTE) PE.AssocLeft
          , PE.Infix (tkc '>' $> EBinop PoGT) PE.AssocLeft
          , PE.Infix (tkc '<' $> EBinop PoLT) PE.AssocLeft
          ]
        , [ PE.Infix (long "==" $> EBinop PoEq) PE.AssocLeft
          , PE.Infix (long "!=" $> EBinop PoNeq) PE.AssocLeft
          ]
        , [ PE.Infix ((PC.lookAhead (PS.string "&&") <|> (tkc '&' $> "")) $> EBinop PoBitand) PE.AssocLeft ]
        , [ PE.Infix (tkc '^' $> EBinop PoBitxor) PE.AssocLeft ]
        , [ PE.Infix ((PC.lookAhead (PS.string "||") <|> (tkc '|' $> "")) $> EBinop PoBitor) PE.AssocLeft ]
        , [ PE.Infix (long "&&" $> EBinop PoAnd) PE.AssocLeft ]
        , [ PE.Infix (long "||" $> EBinop PoOr) PE.AssocLeft ]
        -- ? :
        , [ PE.Infix (tkc '=' $> EAs) PE.AssocRight ]
        -- , comma op
        ] expr_base
        where
        long op = PS.string op <* PS.skipSpaces

    stmt :: ParP ProgF
    stmt = PC.choice
      [ PC.try $ ProgSeq <$> declstmt
      , PC.try $ do
          PS.string "while" *> PS.skipSpaces
          _ <- tkc '('
          c <- expr
          _ <- tkc ')'
          b <- block <|> stmt
          pure $ ProgWhile c b
      , PC.try $ do
          PS.string "for" *> PS.skipSpaces
          _ <- tkc '('
          ei <- expr
          _ <- tkc ';'
          ec <- expr
          _ <- tkc ';'
          ef <- expr
          _ <- tkc ')'
          b <- block <|> stmt
          pure $ ProgFor ei ec ef b
      , PC.try $ do
          PS.string "if" *> PS.skipSpaces
          _ <- tkc '('
          c <- expr
          _ <- tkc ')'
          b <- block <|> stmt
          els <- PC.optionMaybe $ do
            PS.string "else" *> PS.skipSpaces
            block <|> stmt
          pure $ case els of
            Nothing -> ProgIf c b
            Just b' -> ProgIfElse c b b'
      , PC.try $ do
          PS.string "switch" *> PS.skipSpaces
          c <- tkc '(' *> expr <* tkc ')'
          _ <- tkc '{'
          xs <- manyRec $ PC.choice
            [ do
                PS.string "case" *> PS.skipSpaces
                n <- number
                _ <- tkc ':'
                b <- manyRec stmt
                pure $ Tuple (Just $ VInt n) $ ProgSeq b
            , do
                PS.string "default" *> PS.skipSpaces
                _ <- tkc ':'
                b <- manyRec stmt
                pure $ Tuple Nothing $ ProgSeq b
            ]
          _ <- tkc '}'
          pure $ ProgSwitch c xs
      , PC.try $ do
          PS.string "return" *> PC.skipMany1 PT.space
          ProgRet <$> expr <* tkc ';'
      , PC.try $ PS.string "break" *> PS.skipSpaces *> tkc ';' $> ProgBreak
      , PC.try $ PS.string "continue" *> PS.skipSpaces *> tkc ';' $> ProgContinue
      , ProgExpr <$> expr <* tkc ';'
      ]

    declstmt :: ParP (List ProgF)
    declstmt = do
      type_name *> PC.skipMany1 PT.space
      ds <- PC.sepBy1 vdecl $ tkc ','
      _ <- tkc ';'
      pure ds

    vdecl :: ParP ProgF
    vdecl = PC.choice
      [ PC.try $ do
          id <- ident
          _ <- tkc '[' *> tkc ']' *> tkc '='
          _ <- tkc '{'
          vs <- PC.sepBy number $ tkc ','
          _ <- tkc '}'
          pure $ ProgExpr $ EAs (EId id) $ EConst $ VArray $ toUnfoldable $ map VInt vs
      , PC.try $ do
          id <- ident
          _ <- tkc '['
          len <- PC.optionMaybe expr
          _ <- tkc ']'
          pure $ case len of
            Just len' -> ProgAllocAry id len'
            Nothing -> ProgAllocVar id
      , PC.try $ do
          id <- ident
          _ <- tkc '='
          e <- expr
          pure $ ProgExpr $ EAs (EId id) e
      , ProgAllocVar <$> ident
      ]

    block :: ParP ProgF
    block = do
      _ <- tkc '{'
      stmts <- manyRec stmt
      _ <- tkc '}'
      pure $ ProgSeq stmts

    type_name :: ParP String
    type_name = do
      PC.choice $
        [ PS.string "int"
        , PS.string "void"
        , PS.string "char"
        ]

examples :: List (Tuple String String)
examples = fromFoldable
  [ Tuple "Hello world" """
int main() {
  printf("Hello world!\n");
}
"""
  , Tuple "La risposta" """
int main() {
  int x = 42;
  printf("x: %d\n", x);
}
"""
  , Tuple "Numeri triangolari" """
int tri(int n) {
  int x=i=0;
  while (i<n+1) {
    x = x+i;
    i = i+1;
  }
  return x;
}

int main() {
  int i=0;
  while (i < 8) {
    printf("tri(%d) = %d\n", i, tri(i));
    i = i+1;
  }
}
"""
  , Tuple "Euclide - ricorsivo" """
int gcd(int a, int b) {
  if (b == 0) return a;
  printf("GCD(%d,%d) = ?\n", a, b);
  int r = gcd(b, a%b);
  printf("GCD(%d,%d) = %d\n", a, b, r);
  return r;
}

int main() {
  int a=11, b=19;
  printf("Result: %d\n", gcd(a,b));
}
"""
  , Tuple "Euclide - iterativo" """
int gcd(int a, int b) {
  int t;
  int a0=a, b0=b;
  while (b != 0) {
    printf("Current state: %d,%d\n", a, b);
    t = a;
    a = b;
    b = t % b;
  }
  printf("GCD(%d,%d) = %d\n", a0, b0, a);
  return a;
}

int main() {
  int a=11, b=19;
  printf("Result: %d\n", gcd(a,b));
}
"""
  , Tuple "Array" """
void double(int a[], int len) {
  for (i=0; i<len; i++) {
    a[i] = 2*a[i];
  }
}

void print(int a[], int len) {
  printf("[");
  for (i=0; i<len-1; i++)
    printf("%d, ", a[i]);
  printf("%d]\n", a[i]);
}

int main() {
  int a[] = {1,2,3,4,5,6,7};
  double(a, 7);
  print(a, 7);

  double(a, 3);
  print(a, 7);
  print(a, 5);
}
"""
  , Tuple "Tartaglia" """
void tartaglia(int in[], int out[], int len) {
  out[0] = 1;
  for (i=1; i<len; i++) {
    out[i] = in[i-1] + in[i];
  }
  out[i] = 1;
}

void print(int a[], int len) {
  printf("[");
  for (i=0; i<len-1; i++)
    printf("%d, ", a[i]);
  printf("%d]\n", a[i]);
}

int main() {
  int n=10, i;
  int a[n];
  int b[n];

  for (i=0; i<n; i++) {
    if (i%2) {
      tartaglia(b, a, i);
      print(a, i+1);
    }
    else {
      tartaglia(a, b, i);
      print(b, i+1);
    }
  }
}
"""
  , Tuple "Natale" """
void pr(int x[], int n) {
  int i;
  for(i=0; i<n; i++) printf(x);
}

int main() {
  int n=6, i, j;

  for (i=0; i<n; i++) {
    pr(" ", n-i-1);
    pr("*", 2*i+1);
    printf("\n");
  }
  pr(" ", n-1);
  printf("#\n");
}
"""
  ]

type RunS = { config :: Config, nxfrid :: Int }

type RunW = List Config

{-
foldRunw :: RunW -> List (Tuple Config String)
foldRunw xs = snd $ evalRWS (for_ xs go) unit (Tuple (Config Nil) "")
  where
  go :: Either Config String -> RWS Unit (List (Tuple Config String)) (Tuple Config String) Unit
  go x = do
    Tuple sc ss <- get
    let
      s' = case x of
        Left c -> Tuple c ss
        Right s -> Tuple sc $ ss <> s
    put s'
    tell $ singleton s'
-}

trace :: Config -> RunM Unit
trace c = lift <<< lift $ tell $ singleton c

output :: String -> RunM Unit
output s = do
  Config c <- gets _.config
  let c' = Config $ c { stdout = c.stdout <> s }
  lift <<< lift $ tell $ singleton c'
  modify_ _{ config = c' }

printf :: String -> List Val -> String
printf ft xs = snd $ execRWS (runParserT ft p) unit xs
  where
    p :: ParserT String (RWS Unit String (List Val)) Unit
    p = do
      copy <|> format
      p

    copy = do
      c <- PS.noneOf ['%']
      lift $ tell $ SCU.singleton c

    format = do
      _ <- PS.char '%'
      f <- PS.anyChar
      case f of
        'd' -> lift $ do
          mx <- get
          case mx of
            Cons x ys -> do
              tell $ show x
              put ys
            Nil -> pure unit
        '%' -> lift $ tell $ SCU.singleton '%'
        _ -> pure unit

scanf :: String -> String -> Tuple (List Val) String
scanf ft inp = case runParser inp (runParserT ft p) of
  Right (Right x) -> x
  _ -> Tuple Nil inp
  where
  p :: ParserT String (Parser String) (Tuple (List Val) String)
  p = do
    _ <- PS.char '%'
    PS.anyChar >>= case _ of
      'd' -> lift $ do
        _<- PS.skipSpaces
        x <- number
        (ParseState s _ _) <- get
        pure $ Tuple (singleton $ VInt x) s
      _ -> do
        (ParseState s _ _) <- lift get
        pure $ Tuple Nil s

  number = do
    xs <- map ((\x -> x-0x30) <<< toCharCode) <$> someRec PT.digit <* PS.skipSpaces
    pure $ conv xs 0
    where
    conv Nil n = n
    conv (x:xs) n = conv xs (10*n + x)

type RunM a = ExceptT String (ContT Unit (RWS Prog RunW RunS)) a
type RK = Val -> RunM Val

runm :: ProgF -> RK -> RK -> RK -> RunM Val
runm p kr kbr kcn = case p of
  ProgExpr e -> ceval e
  ProgCall id args -> do
    prog <- ask
    let prog_fs = flip map prog $ \{fname: f, argns: as, code: c} -> Tuple f (Tuple as c)
    argsval <- for args ceval
    case lookup id prog_fs of
      Just (Tuple as f) -> do
        { config: Config c, nxfrid: nxfrid } <- get
        let
          fr = case as of
            Argdef as' -> { name: id, env: Map.fromFoldable $ zip as' argsval, frid: nxfrid }
            Argvar as' ->
              let
                env = Map.fromFoldable $ zip as' argsval
                vargs = VArray <<< toUnfoldable $ drop (length as') argsval
                venv = Map.insert "#varargs" vargs env
              in { name: id, env: venv, frid: nxfrid }
          y = Config $ c{ frs = fr : c.frs }
        trace y
        put { config: y, nxfrid: nxfrid + 1 }
        v <- callCC $ \kr' -> runm f kr' kbr kcn
        modify_ $ \s ->
          let
            Config c' = s.config
            frs' = case tail c'.frs of
              Just x -> x
              Nothing -> Nil
            c'' = Config $ c' { frs = frs' }
          in
            s { config = c'' }
        gets _.config >>= trace
        pure v
      Nothing -> pure VVoid -- should be unreachable (func name not in prog)
  ProgRet e -> ceval e >>= kr
  ProgAllocVar id -> do
    fr <- framegettop
    let env' = Map.insert id VUndef fr.env
    frameput fr.frid $ fr { env = env' }
    pure VVoid
  ProgAllocAry id len -> do
    fr <- framegettop
    ceval len >>= case _ of
      VInt len' -> do
        let env' = Map.insert id (VArray $ A.replicate len' VUndef) fr.env
        frameput fr.frid $ fr { env = env' }
      _ -> throwError "alloc array size must be int"
    pure VVoid
  ProgIOW -> do
    frtop <- framegettop
    let frid = frtop.frid
    ftref <- readlval $ LVAtom frid "format"
    vs <- case Map.lookup "#varargs" frtop.env of
      Just (VArray vs') -> pure $ fromFoldable vs'
      Just _ -> throwError "invalid varargs array"
      Nothing -> pure $ Nil
    case ftref of
      VRef (LVAtom frid' id) -> do
        fr <- frameget frid'
        case Map.lookup id fr.env of
          Just (VArray cs) -> do
            let
              getvint (VInt x) = Just x
              getvint _ = Nothing
              fts = fromCharArray <$> traverse (fromCharCode <=< getvint) cs
            case fts of
              Just fts' -> output $ printf fts' vs
              Nothing -> throwError "printf: can't convert format string"
          _ -> throwError "printf: format string is not a valid string"
      _ -> throwError "printf: format string is not a valid ref"
    pure VVoid
  ProgIOR -> do
    frtop <- framegettop
    let frid = frtop.frid
    ftref <- readlval $ LVAtom frid "format"
    case ftref of
      VRef (LVAtom frid' id) -> do
        fr <- frameget frid'
        case Map.lookup id fr.env of
          Just (VArray cs) -> do
            let
              getvint (VInt x) = Just x
              getvint _ = Nothing
              fts = fromCharArray <$> traverse (fromCharCode <=< getvint) cs
            case fts of
              Just fts' -> do
                inp <- gets $ (\(Config c) -> c.stdin) <<< _.config
                let Tuple vs inp' = scanf fts' inp
                Config c <- gets _.config
                let c' = Config $ c { stdin = inp' }
                modify_ _{ config = c' }
                trace c'
                refs <- case Map.lookup "#varargs" frtop.env of
                  Just (VArray vs') -> pure $ fromFoldable vs'
                  Just _ -> throwError "invalid varargs array"
                  Nothing -> pure $ Nil
                for_ (zip refs vs) $ \x -> do
                  case x of
                    Tuple (VRef r') v -> writelval r' v
                    _ -> pure unit
              Nothing -> throwError "printf: can't convert format string"
          _ -> throwError "printf: format string is not a valid string"
      _ -> throwError "printf: format string is not a valid ref"
    pure VVoid
  ProgSeq xs -> do
    for_ xs $ \x -> runm x kr kbr kcn
    pure VVoid
  ProgWhile e x -> do
    b <- ceval e
    case b of
      VInt 0 -> pure VVoid
      _ -> do
        callCC $ \kbr' -> do
          _ <- callCC $ \kcn' -> runm x kr kbr' kcn'
          runm p kr kbr' kcn
  ProgFor ei ec ef x -> do
    _ <- ceval ei
    let
      go = do
        b <- ceval ec
        case b of
          VInt 0 -> pure VVoid
          _ -> do
            callCC $ \kbr' -> do
              _ <- callCC $ \kcn' -> runm x kr kbr' kcn'
              _ <- ceval ef
              go
    go
  ProgIf e x -> do
    b <- ceval e
    case b of
      VInt 0 -> pure VVoid
      _ -> runm x kr kbr kcn
  ProgIfElse e x x' -> do
    b <- ceval e
    case b of
      VInt 0 -> runm x' kr kbr kcn
      _ -> runm x kr kbr kcn
  ProgSwitch e bs -> do
    swv <- ceval e
    callCC $ \kbr' -> do
      let
        go true xs = runm (ProgSeq (map snd xs)) kr kbr' kcn
        go false Nil = pure VVoid
        go false xs@((Tuple Nothing _):_) = go true xs
        go false all@((Tuple (Just v) _) : xs) = case swv, v of
            VInt swvi, VInt vi ->
              if vi == swvi
              then go true all
              else go false xs
            _, _ -> pure VVoid
      go false bs
  ProgBreak -> kbr VVoid
  ProgContinue -> kcn VVoid

prepare :: String -> Maybe (Tuple Prog Config)
prepare = parse <<< preprocessor

execprog :: String -> Tuple Prog Config -> RunW
execprog stdin p =
  let RWSResult s a w = go p
  in w
  where
  go :: Tuple Prog Config -> RWSResult RunS Unit RunW
  go (Tuple prog (Config static)) =
    let r = runExceptT $ runm (ProgCall "main" Nil) pure pure pure
    in runRWS
      (runContT r (\_ -> pure unit))
      (prog <> stdlib)
      { config: Config $ static { stdin = stdin }, nxfrid: 1 }

type HState =
  { text :: String
  , trace :: RunW
  , tstep :: Int
  }

data Query a
  = Step Int a
  | HSelTime Int a
  | HRun a
  | HLoad a
  | IsOn (HState -> a)

type Input = Unit

data Message = Toggled Boolean

myComp :: forall m. MonadEffect m => H.Component HH.HTML Query Input Message m
myComp =
  H.component
    { initialState: const initialState
    , render
    , eval
    , receiver: const Nothing
    }
  where

  initialState :: HState
  initialState =
    let
      text = fromMaybe "" $ snd <$> head examples
      tr = fromMaybe Nil $ execprog "" <$> prepare text
    in { text: text , trace: tr , tstep: 0 }

  render :: HState -> H.ComponentHTML Query
  render state =
    HH.div_ $
      [ HH.div
        [ HP.attr (HC.AttrName "style")
            $  "white-space: nowrap; overflow: scroll;"
            <> "padding-bottom: 20px;"
        ]
        [ HH.div
          [ HP.attr (HC.AttrName "style")
              $  "display: inline-block;"
              <> "vertical-align: top;"
              <> "margin-left: 2px;"
              <> "margin-right: 2px;"
          ]
          [ HH.div_
            [ HH.textarea
              [ HP.value state.text
              , HP.ref $ H.RefLabel "editor"
              , HP.attr (HC.AttrName "style") "font-family: monospace;"
              , HP.rows 30
              , HP.cols 40
              ]
            ]
          , HH.div_
            [ HH.text "Select example "
            , HH.select
              [ HP.ref $ H.RefLabel "examplesel" ]
              $ toUnfoldable $ flip map examples $ \x ->
                  HH.option_ [ HH.text $ fst x ]
            , HH.button
              [ HE.onClick $ HE.input_ HLoad ]
              [ HH.text "load" ]
            ]
          ]
        , HH.div
          [ HP.attr (HC.AttrName "style")
              $  "display: inline-block;"
              <> "vertical-align: top;"
              <> "margin-left: 2px;"
              <> "margin-right: 2px;"
          ]
          [ HH.button
            [ HE.onClick $ HE.input_ HRun
            , HP.attr (HC.AttrName "style")
                $  "width: 50px;"
                <> "height: 50px;"
                <> "background: chartreuse"
            ]
            [ HH.text "run" ]
          ]
        , HH.div
            [ HP.attr (HC.AttrName "style")
                $  "display: inline-block;"
                <> "vertical-align: top;"
                <> "width: 350px;"
                <> "margin-left: 2px;"
                <> "margin-right: 2px;"
            ]
            [ HH.div_
                [ HH.div_ [ HH.text "Input"]
                , HH.div
                    [ HP.attr (HC.AttrName "style")
                        $  "font-family: monospace;"
                        <> "color: black;"
                        <> "padding: 5px;"
                    ]
                    [ HH.div_
                        [ HH.textarea
                            [ HP.value "42"
                            , HP.ref $ H.RefLabel "stdin"
                            , HP.attr (HC.AttrName "style")
                                $  "font-family: monospace;"
                                <> "width: 100%;"
                                <> "height: 100;"
                            ]
                        ]
                    ]
                ]
            , HH.div
                [ HP.attr (HC.AttrName "style")
                    $  "background: ivory;"
                    <> "overflow-x: scroll"
                ]
                [ HH.div
                    [ HP.attr (HC.AttrName "style")
                        $  "background: honeydew;"
                        <> "color: black;"
                        <> "margin: 5px;"
                    ]
                    [ HH.text "Input stream"]
                , HH.div
                    [ HP.attr (HC.AttrName "style")
                        $  "font-family: monospace;"
                        <> "color: black;"
                        <> "padding: 5px;"
                    ]
                    [ HH.pre
                      [ HP.attr (HC.AttrName "style") "margin: 0px;" ]
                      [ HH.text $ fromMaybe "" $ (\(Config c) -> c.stdin) <$> state.trace !! state.tstep ]
                    ]
                ]
            , HH.div
                [ HP.attr (HC.AttrName "style")
                    $  "background: black;"
                    <> "overflow-x: scroll"
                ]
                [ HH.div
                    [ HP.attr (HC.AttrName "style")
                        $  "background: purple;"
                        <> "color: white;"
                        <> "margin: 5px;"
                    ]
                    [ HH.text "Output stream"]
                , HH.div
                    [ HP.attr (HC.AttrName "style")
                        $  "font-family: monospace;"
                        <> "color: lime;"
                        <> "padding: 5px;"
                    ]
                    [ HH.pre
                      [ HP.attr (HC.AttrName "style") "margin: 0px;" ]
                      [ HH.text $ fromMaybe "" $ (\(Config c) -> c.stdout) <$> state.trace !! state.tstep ]
                    ]
                ]
            ]
        , HH.div
          [ HP.attr (HC.AttrName "style")
              $  "display: inline-block;"
              <> "vertical-align: top;"
              <> "margin-left: 2px;"
              <> "margin-right: 2px;"
          ]
          [ HH.div_ [ HH.text "Time travel (or click on the time series below)" ]
          , HH.div_
              [ HH.button [ HE.onClick (HE.input_ $ Step (-1)) ] [ HH.text "<" ]
              , HH.text $ " " <> show state.tstep <> " "
              , HH.button [ HE.onClick (HE.input_ $ Step 1) ] [ HH.text ">" ]
              ]
          , HH.div
              [ HP.attr (HC.AttrName "style")
                  "height: 300px;"
              ]
              [ case state.trace !! state.tstep of
                  Just c -> r_timestep Nothing c
                  Nothing -> HH.div_ []
              ]
          ]
        ]
      , HH.div
          [ HP.attr (HC.AttrName "style")
              $  "white-space: nowrap; overflow: scroll;"
              <> "padding-bottom: 20px;"
          ]
          $ flip A.mapWithIndex (toUnfoldable state.trace)
            $ \i c -> r_timestep (Just i) c
      ]
    where
    r_timestep :: Maybe Int -> Config -> H.ComponentHTML Query
    r_timestep i (Config s) = HH.div
      [ HE.onClick $ HE.input_ $ HSelTime $ fromMaybe state.tstep i
      , HP.attr (HC.AttrName "style")
          $  "display: inline-block;"
          <> "vertical-align: bottom;"
          <> case i of
                Just _ -> "width: 250px; margin: 5px;"
                Nothing -> ""
          -- <> "overflow: scroll;"
      ] $
      [ HH.div_ $ flip map (toUnfoldable s.frs) $ \fr ->
          HH.div
            [ HP.attr (HC.AttrName "style")
                $  "background: peachpuff;"
                <> "margin: 2px;"
                <> "padding: 2px;"
            ]
            [ HH.div
                [ HP.attr (HC.AttrName "style")
                    $  "font-family: sans-serif; font-size: 12;"
                    <> "margin: 5px;"
                    <> "background: tomato;"
                ]
                [ HH.text $ "(" <> show fr.frid <> ") " <> fr.name ]
            , HH.div
                [ HP.attr (HC.AttrName "style")
                    $  "font-family: monospace; font-size: 14;"
                    <> "overflow: scroll;"
                    <> "padding: 5px;"
                ]
                $ map f (Map.toUnfoldable fr.env)
            ]
      ]
      <> case i of
        Just i' -> [ HH.div_ [ HH.text $ "t: " <> show i' ] ]
        Nothing -> []

    f (Tuple k v) = HH.div_ [ HH.text $ k <> ": " <> show v ]

  eval :: Query ~> H.ComponentDSL HState Query Message m
  eval = case _ of
    Step x next -> do
      state <- H.get
      let nextState = state { tstep = state.tstep + x }
      H.put nextState
      H.raise $ Toggled true
      pure next
    HSelTime x next -> do
      state <- H.get
      H.put $ state { tstep = x }
      pure next
    HRun next -> do
      H.getHTMLElementRef (H.RefLabel "editor") >>= case _ of
        Nothing -> pure unit
        Just el -> case HTextArea.fromHTMLElement el of
          Nothing -> pure unit
          Just t -> H.getHTMLElementRef (H.RefLabel "stdin") >>= case _ of
            Nothing -> pure unit
            Just el2 -> case HTextArea.fromHTMLElement el2 of
              Nothing -> pure unit
              Just t_in -> do
                text <- H.liftEffect $ HTextArea.value t
                inp <- H.liftEffect $ HTextArea.value t_in
                let tr = fromMaybe Nil $ execprog inp <$> prepare text
                H.put { text: text, trace: tr, tstep: 0 }
      pure next
    HLoad next -> do
      H.getHTMLElementRef (H.RefLabel "examplesel") >>= case _ of
        Nothing -> pure unit
        Just el -> case HSelect.fromHTMLElement el of
          Nothing -> pure unit
          Just s -> do
            H.getHTMLElementRef (H.RefLabel "editor") >>= case _ of
              Nothing -> pure unit
              Just el2 -> case HTextArea.fromHTMLElement el2 of
                Nothing -> pure unit
                Just t -> do
                  v <- H.liftEffect $ HSelect.value s
                  H.liftEffect $ HTextArea.setValue
                    (fromMaybe "" $ lookup v examples) t
      pure next
    IsOn reply -> do
      state <- H.get
      pure (reply state)

main :: Effect Unit
main = do
  log "Hello 🍝!"
  HA.runHalogenAff do
    body <- HA.awaitBody
    runUI myComp unit body
