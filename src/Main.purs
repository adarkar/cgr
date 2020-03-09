module Main where

import Prelude

import Effect (Effect)
import Effect.Console (log)
import Effect.Class (class MonadEffect)

import Data.Maybe (Maybe(..))
import Data.List
  ( List(..), (:), (!!), span, singleton, find, zip, fromFoldable, drop
  , length, toUnfoldable, head, tail
  , manyRec, someRec)
import Data.Either (Either(..))
import Data.Map as Map
import Data.Array (updateAt)
import Data.Array as A
import Data.Char (toCharCode, fromCharCode)
import Data.String.CodeUnits (fromCharArray)
import Data.String.CodeUnits as SCU
import Data.Tuple (Tuple(..), lookup, snd)
-- import Data.Unfoldable
import Data.Foldable (for_)
import Data.Traversable (for, traverse)

import Control.Alt ((<|>))
import Control.Monad.State (State, runState)
import Control.Monad.RWS (RWS, tell, ask, get, gets, put, modify_, runRWS, execRWS, RWSResult(..))
import Control.Monad.Cont (ContT, callCC, runContT)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Trans.Class (lift)

import Text.Parsing.Parser (ParserT, runParserT)
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

data Val =
    VVoid
  | VInt Int
  | VFloat Number
  | VArray (Array Val)
  | VRef LVal

instance showVal :: Show Val where
  show VVoid = "void"
  show (VInt x) = show x
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
  PoAdd | PoMul | PoLT

data PrimopUn = PoNeg

primopBin :: PrimopBin -> Int -> Int -> Int
primopBin op = case op of
  PoAdd -> (+)
  PoMul -> (*)
  PoLT -> \a b -> if a < b then 1 else 0

data Expr =
    EId String
  | EConst Val
  | ESubscr Expr Expr
  | EAs Expr Expr
  | ECall String (List Expr)
  | EBinop PrimopBin Expr Expr
  | EUnop PrimopUn Expr
  | ETernop Expr Expr Expr

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
  EUnop _ _ -> pure VVoid
  ETernop _ _ _ -> pure VVoid

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
    let env' = Map.update up id fr.env
    frameput frid $ fr { env = env' }
    where
      up ary = case ary of
        VArray ary' -> VArray <$> updateAt ix v ary'
        _ -> Nothing

data ProgF =
    ProgExpr Expr
  | ProgCall String (List Expr)
  | ProgRet Expr
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

{-
test_prog_main :: ProgF
test_prog_main = ProgSeq $ fromFoldable
  [ ProgExpr $ EAs { loc: EId "i", val: EConst $ VInt 0 }
  , ProgOp $ EAs { loc: EId "x", val: EConst $ VInt 0 }
  , ProgWhile (EBinop PoLT (EId "i") (EConst $ VInt 5)) $ ProgSeq $ fromFoldable
    [ ProgOp $ As { loc: EId "x", val: EBinop PoAdd (EId "x") (EId "i") }
    , ProgOp $ As { loc: EId "i", val: EBinop PoAdd (EId "i") (EConst $ VInt 1) }
    ]
  , ProgOp $ As { loc: EId "a", val: ECall "foo" $
      fromFoldable [EBinop PoAdd (EId "x") (EConst $ VInt 1)] }
  , ProgOp $ Call "printf" $ fromFoldable $ map (EConst <<< VInt) [0,1,2]
  , ProgOp $ As { loc: EId "ar", val: EConst $ VArray $ map VInt [0,0,0,0,0,0] }
  , ProgOp $ Call "fib" $ fromFoldable [EId "ar", EConst $ VInt 6]
  , ProgOp $ Ret $ EConst $ VInt 0
  ]

test_prog_foo :: ProgF
test_prog_foo = ProgSeq $ fromFoldable
  [ ProgOp $ As { loc: EId "i", val: EBinop PoAdd (EId "i") (EConst $ VInt 6) }
  , ProgOp $ Ret $ EBinop PoAdd (EId "i") (EConst $ VInt 2)
  , ProgOp $ As { loc: EId "i", val: EConst $ VInt 4 }
  ]

test_prog_fib :: ProgF
test_prog_fib = ProgSeq $ fromFoldable
  [ ProgOp $ As { loc: EId "i", val: EConst $ VInt 0 }
  , ProgWhile (EBinop PoLT (EId "i") (EId "len")) $ ProgSeq $ fromFoldable
    [ ProgOp $ As { loc: ESubscr (EId "a") (EId "i"), val: EId "i" }
    , ProgOp $ As { loc: EId "i", val: EBinop PoAdd (EId "i") (EConst $ VInt 1) }
    ]
  ]

test_prog :: Prog
test_prog = fromFoldable
  [ { fname: "main", argns: Argdef Nil, code: test_prog_main }
  , { fname: "foo", argns: Argdef $ fromFoldable ["i"], code: test_prog_foo }
  , { fname: "fib", argns: Argdef $ fromFoldable ["a", "len"], code: test_prog_fib }
  ]
-}

stdlib :: Prog
stdlib = fromFoldable
  [ { fname: "printf", argns: Argvar $ fromFoldable ["format"], code: stdlib_printf }
  ]
  where
    stdlib_printf :: ProgF
    stdlib_printf = ProgIOW

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
      r <- manyRec PT.alphaNum
      PS.skipSpaces
      pure $ fromCharArray [f] <> fromCharArray (toUnfoldable r)

    tkc :: Char -> ParP Char
    tkc c = PS.char c <* PS.skipSpaces

    func :: ParP { fname :: String, argns :: Argdef, code :: ProgF }
    func = do
      _ <- PS.skipSpaces *> type_name *> PC.skipMany1 PT.space
      fname <- ident
      _ <- tkc '('
      args <- PC.sepBy ident (tkc ',')
      _ <- tkc ')'
      _ <- tkc '{'
      stmts <- manyRec stmt
      _ <- tkc '}'
      pure $ { fname: fname, argns: Argdef args, code: ProgSeq stmts }

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
            cs <- toUnfoldable <$> manyRec (PS.noneOf ['"'])
            _ <- tkc '"'
            { fr: stfr, nxid: stid } <- lift get
            let
              idname = "#s:" <> show stid
              ary = VArray $ map (VInt <<< toCharCode) cs
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
      expr_tree = do
        PE.buildExprParser
          [ [ PE.Infix (tkc '*' $> EBinop PoMul) PE.AssocRight ]
          , [ PE.Infix (tkc '+' $> EBinop PoAdd) PE.AssocRight ]
          , [ PE.Infix (tkc '<' $> EBinop PoLT) PE.AssocRight ]
          , [ PE.Infix (tkc '=' $> EAs) PE.AssocRight ]
          ] expr_base

    stmt :: ParP ProgF
    stmt = PC.choice
      [ PC.try $ do
          PS.string "while" *> PS.skipSpaces
          _ <- tkc '('
          c <- expr
          _ <- tkc ')'
          b <- block <|> stmt
          pure $ ProgWhile c b
      , PC.try $ do
          PS.string "return" *> PC.skipMany1 PT.space
          ProgRet <$> expr <* tkc ';'
      , ProgExpr <$> expr <* tkc ';'
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
        ]

hello_world :: String
hello_world = """
int main() {
  printf("Hello world!");
}
"""

test_prog_2 :: String
test_prog_2 = """
int foo (x) {
  return x+2;
}

int main(foo, bar) {
  h = "hello";
  q = h[0];
  h[0] = 72;
  x = 11;
  i = 8;
  x = x + i;
  i = 10 + x * 2;
  i = (10+x) * 2;
  printf("ciao ");
  printf(h);
  printf(" i: %d, x: %d ", i, x);
  i = 0;
  while (i < 3) {
    i = i+1;
  }
  x = foo(i);
}
"""

test_prog_1 = """
int foo (x) {
  i = 0;
  y = 0;
  while (i < x+1) {
    y = y+i;
    i = i+1;
  }
  return y;
}

int main(foo, bar) {
  h = "hello";
  h[0] = 72;
  printf(h);

  x = foo(3);
  printf(" x: %d", x);
}
"""

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
      progtext = state.text
      RunW tr out = case parse progtext of
        Just x -> runm2lconfig $ test_runm x
        Nothing -> RunW Nil ""
    in
    HH.div_ $
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
        [ HH.button [ HE.onClick $ HE.input_ $ HRun ] [ HH.text "run" ] ]
      , HH.button [ HE.onClick (HE.input_ $ Step (-1)) ] [ HH.text "<" ]
      , HH.text $ " " <> show state.tstep <> " "
      , HH.button [ HE.onClick (HE.input_ $ Step 1) ] [ HH.text ">" ]
      , HH.div_ [ HH.text $ "Out: " <> out ]
      , HH.div
          [ HP.attr (HC.AttrName "style")
              "height: 300px;"
          ]
          [ case tr !! state.tstep of
              Just conf -> r_timestep Nothing conf
              Nothing -> HH.div_ []
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
          <> "width: 250px;"
          -- <> "overflow: scroll;"
          <> "margin: 5px;"
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
            -- H.liftEffect $ HTextArea.setValue "ciao" t
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
