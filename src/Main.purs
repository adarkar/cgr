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

import Text.Parsing.Parser (ParserT, runParserT, Parser, runParser)
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

data Config = Config (List Frame)

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
  ECall id args -> runm (ProgCall id args) pure
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

leval :: Expr -> RunM LVal
leval e = case e of
  EId id -> do
    Config c <- gets _.config
    case head c of
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
  let { init: frin, rest: frrs } = span (\fr -> fr.frid /= frid) c
  case frrs of
    Nil -> throwError "frame not found"
    fr : below -> do
      let y = Config $ frin <> singleton fr' <> below
      trace y
      modify_ $ _{ config = y }

frameget :: Int -> RunM Frame
frameget frid = do
  Config c <- gets _.config
  case flip find c (\fr -> fr.frid == frid) of
    Just x -> pure x
    Nothing -> throwError "frame not found"

framegettop :: RunM Frame
framegettop = do
  Config c <- gets _.config
  case head c of
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
  | ProgIOR String (List Int)
  | ProgSeq (List ProgF)
  | ProgWhile Expr ProgF
  | ProgIf Expr ProgF
  | ProgIfElse Expr ProgF ProgF

data Argdef =
    Argdef (List String)
  | Argvar (List String)

type Prog = List { fname :: String, argns :: Argdef, code :: ProgF }

stdlib :: Prog
stdlib = fromFoldable
  [ { fname: "printf", argns: Argvar $ fromFoldable ["format"], code: stdlib_printf }
  ]
  where
    stdlib_printf :: ProgF
    stdlib_printf = ProgIOW

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
  Tuple (Right x) s -> Just $ Tuple x $ Config $ singleton s.fr
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
          ]
        , [ PE.Infix (tkc '*' $> EBinop PoMul) PE.AssocRight
          , PE.Infix (tkc '/' $> EBinop PoDiv) PE.AssocRight
          , PE.Infix (tkc '%' $> EBinop PoMod) PE.AssocRight
          ]
        , [ PE.Infix (tkc '+' $> EBinop PoAdd) PE.AssocRight
          , PE.Infix (tkc '-' $> EBinop PoSub) PE.AssocRight
          ]
        , [ PE.Infix (long "<<" $> EBinop PoShL) PE.AssocRight
          , PE.Infix (long ">>" $> EBinop PoShR) PE.AssocRight
          ]
        , [ PE.Infix (long ">=" $> EBinop PoGTE) PE.AssocRight
          , PE.Infix (long "<=" $> EBinop PoLTE) PE.AssocRight
          , PE.Infix (tkc '>' $> EBinop PoGT) PE.AssocRight
          , PE.Infix (tkc '<' $> EBinop PoLT) PE.AssocRight
          ]
        , [ PE.Infix (long "==" $> EBinop PoEq) PE.AssocRight
          , PE.Infix (long "!=" $> EBinop PoNeq) PE.AssocRight
          ]
        , [ PE.Infix ((PC.lookAhead (PS.string "&&") <|> (tkc '&' $> "")) $> EBinop PoBitand) PE.AssocRight ]
        , [ PE.Infix (tkc '^' $> EBinop PoBitxor) PE.AssocRight ]
        , [ PE.Infix ((PC.lookAhead (PS.string "||") <|> (tkc '|' $> "")) $> EBinop PoBitor) PE.AssocRight ]
        , [ PE.Infix (long "&&" $> EBinop PoAnd) PE.AssocRight ]
        , [ PE.Infix (long "||" $> EBinop PoOr) PE.AssocRight ]
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
          PS.string "if" *> PS.skipSpaces
          _ <- tkc '('
          c <- expr
          _ <- tkc ')'
          b <- block <|> stmt
          pure $ ProgIf c b
      , PC.try $ do
          PS.string "return" *> PC.skipMany1 PT.space
          ProgRet <$> expr <* tkc ';'
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
          _ <- tkc '['
          len <- expr
          _ <- tkc ']'
          pure $ ProgAllocAry id len
      , PC.try $ do
          id <- ident
          _ <- tkc '[' *> tkc ']' *> tkc '='
          _ <- tkc '{'
          vs <- PC.sepBy number $ tkc ','
          _ <- tkc '}'
          pure $ ProgExpr $ EAs (EId id) $ EConst $ VArray $ toUnfoldable $ map VInt vs
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

hello_world :: String
hello_world = """
int main() {
  printf("Hello world!\n");
}
"""

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
  ]

type RunS = { config :: Config, nxfrid :: Int }

data RunW = RunW (List Config) String

instance monoidRunW :: Monoid RunW where
  mempty = RunW Nil ""

instance semigroupRunW :: Semigroup RunW where
  append (RunW tr1 out1) (RunW tr2 out2) = RunW (tr1 <> tr2) (out1 <> out2)

trace :: Config -> RunM Unit
trace c = lift <<< lift $ tell $ RunW (singleton c) ""

output :: String -> RunM Unit
output s = lift <<< lift $ tell $ RunW Nil s

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

type RunM a = ExceptT String (ContT Unit (RWS Prog RunW RunS)) a

runm :: ProgF -> (Val -> RunM Val) -> RunM Val
runm p k = case p of
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
          y = Config $ fr : c
        trace y
        put { config: y, nxfrid: nxfrid + 1 }
        v <- callCC $ runm f
        modify_ $ \s ->
          let
            Config c' = s.config
            c'' = Config $ case tail c' of
              Just x -> x
              Nothing -> Nil
          in
            s { config = c'' }
        gets _.config >>= trace
        pure v
      Nothing -> pure VVoid -- should be unreachable (func name not in prog)
  ProgRet e -> ceval e >>= k
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
  ProgSeq xs -> do
    for_ xs $ \x -> runm x k
    pure VVoid
  ProgWhile e x -> do
    b <- ceval e
    case b of
      VInt 0 -> pure VVoid
      _ -> runm x k *> runm p k
  ProgIf e x -> do
    b <- ceval e
    case b of
      VInt 0 -> pure VVoid
      _ -> runm x k
  _ -> pure VVoid

test_runm :: Tuple Prog Config -> RWSResult RunS Unit RunW
test_runm (Tuple prog c) =
  let r = runExceptT $ runm (ProgCall "main" Nil) pure
  in runRWS
    (runContT r (\_ -> pure unit))
    (prog <> stdlib)
    { config: c, nxfrid: 1 }

runm2lconfig :: RWSResult RunS Unit RunW -> RunW
runm2lconfig r = let RWSResult s a w = r in w

type HState =
  { text :: String
  , tstep :: Int
  }

data Query a
  = Step Int a
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
  initialState = { text: hello_world, tstep: 0 }

  render :: HState -> H.ComponentHTML Query
  render state =
    let
      progtext = preprocessor state.text
      RunW tr out = case parse progtext of
        Just x -> runm2lconfig $ test_runm x
        Nothing -> RunW Nil ""
    in
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
              <> "width: 250px;"
              <> "margin-left: 2px;"
              <> "margin-right: 2px;"
              <> "background: black;"
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
                [ HH.text out ]
              ]
          ]
        , HH.div
          [ HP.attr (HC.AttrName "style")
              $  "display: inline-block;"
              <> "vertical-align: top;"
              <> "margin-left: 2px;"
              <> "margin-right: 2px;"
          ]
          [ HH.div_ [ HH.text "Time travel" ]
          , HH.div_
              [ HH.button [ HE.onClick (HE.input_ $ Step (-1)) ] [ HH.text "<" ]
              , HH.text $ " " <> show state.tstep <> " "
              , HH.button [ HE.onClick (HE.input_ $ Step 1) ] [ HH.text ">" ]
              ]
          , HH.div
              [ HP.attr (HC.AttrName "style")
                  "height: 300px;"
              ]
              [ case tr !! state.tstep of
                  Just conf -> r_timestep Nothing conf
                  Nothing -> HH.div_ []
              ]
          ]
        ]
      , HH.div
          [ HP.attr (HC.AttrName "style")
              $  "white-space: nowrap; overflow: scroll;"
              <> "padding-bottom: 20px;"
          ]
          $ flip A.mapWithIndex (toUnfoldable tr)
            $ \i c -> r_timestep (Just i) c
      ]
    where
    r_timestep :: Maybe Int -> Config -> H.ComponentHTML Query
    r_timestep i (Config s) = HH.div
      [ HP.attr (HC.AttrName "style")
          $  "display: inline-block;"
          <> "vertical-align: bottom;"
          <> case i of
                Just _ -> "width: 250px; margin: 5px;"
                Nothing -> ""
          -- <> "overflow: scroll;"
      ] $
      [ HH.div_ $ flip map (toUnfoldable s) $ \fr ->
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
    HRun next -> do
      H.getHTMLElementRef (H.RefLabel "editor") >>= case _ of
        Nothing -> pure unit
        Just el -> case HTextArea.fromHTMLElement el of
          Nothing -> pure unit
          Just t -> do
            text <- H.liftEffect $ HTextArea.value t
            H.put { text: text, tstep: 0 }
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
