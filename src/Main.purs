module Main where

import Prelude

import Effect (Effect)
import Effect.Console (log)

import Data.Maybe (Maybe(..))
import Data.List
  ( List(..), (:), span, singleton, find, zip, fromFoldable, drop
  , length, mapWithIndex, toUnfoldable, head, tail
  , manyRec, someRec)
import Data.Either (Either(..))
import Data.Map as Map
import Data.Array ((!!), updateAt)
import Data.Array as A
import Data.Char (toCharCode)
import Data.String.CodeUnits (fromCharArray)
import Data.Tuple (Tuple(..), lookup)
-- import Data.Unfoldable
import Data.Foldable (for_)
import Data.Traversable (for)

import Control.Alt ((<|>))
import Control.Monad.RWS (RWS, tell, ask, get, gets, put, modify_, runRWS, RWSResult(..))
import Control.Monad.Cont (ContT, callCC, runContT)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Trans.Class (lift)

import Text.Parsing.Parser (Parser, runParser)
import Text.Parsing.Parser.String as PS
import Text.Parsing.Parser.Combinators as PC
import Text.Parsing.Parser.Token as PT

import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
-- import Halogen.HTML.Properties as HP
import Halogen.Aff as HA
import Halogen.VDom.Driver (runUI)

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
  show (LVAtom frid id) = "[ref(fr:" <> show frid <> ") " <> id <> "]"
  show (LVAryEl frid id ix) = "[ref(fr:" <> show frid <> ") " <> id <> "[" <> show ix <> "]"

data Op =
    As { loc :: Expr, val :: Expr }
  | Call String (List Expr)
  | Ret Expr
  | IOW
  | IOR String (List Int)

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
  ECall id args -> runm (ProgOp $ Call id args) pure
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
      Just (VArray ar) -> case ar !! ix of
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
    ProgOp Op
  | ProgSeq (List ProgF)
  | ProgWhile Expr ProgF
  | ProgIf Expr ProgF
  | ProgIfElse Expr ProgF ProgF

data Argdef =
    Argdef (List String)
  | Argvar (List String)

type Prog = List { fname :: String, argns :: Argdef, code :: ProgF }

test_prog_main :: ProgF
test_prog_main = ProgSeq $ fromFoldable
  [ ProgOp $ As { loc: EId "i", val: EConst $ VInt 0 }
  , ProgOp $ As { loc: EId "x", val: EConst $ VInt 0 }
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

stdlib_printf :: ProgF
stdlib_printf = ProgOp IOW

stdlib :: Prog
stdlib = fromFoldable
  [ { fname: "printf", argns: Argvar $ fromFoldable ["format"], code: stdlib_printf }
  ]

parse :: String -> Prog
parse input = case runParser input prog of
  Left _ -> Nil
  Right x -> x
  where
    prog :: Parser String Prog
    prog = someRec func

    ident :: Parser String String
    ident = do
      f <- PT.letter <|> PS.char '_'
      r <- manyRec PT.alphaNum
      PS.skipSpaces
      pure $ fromCharArray [f] <> fromCharArray (toUnfoldable r)

    tkc :: Char -> Parser String Char
    tkc c = PS.char c <* PS.skipSpaces

    func :: Parser String { fname :: String, argns :: Argdef, code :: ProgF }
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

    number :: Parser String Int
    number = do
      xs <- map ((\x -> x-0x30) <<< toCharCode) <$> someRec PT.digit
      pure $ conv xs 0
      where
      conv Nil n = n
      conv (x:xs) n = conv xs (10*n + x)

    assign :: Parser String ProgF
    assign = do
      id <- ident
      _ <- tkc '='
      num <- number
      pure $ ProgOp $ As { loc: EId id, val: EConst $ VInt num }

    stmt :: Parser String ProgF
    stmt = do
      as <- assign
      _ <- tkc ';'
      pure as

    type_name :: Parser String String
    type_name = do
      PC.choice $
        [ PS.string "int"
        , PS.string "void"
        ]

test_string :: String
test_string = """
int main(foo, bar) {
  x = 0;
}
"""

test_prog_parsed :: Prog
test_prog_parsed = parse test_string

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

type RunM a = ExceptT String (ContT Unit (RWS Prog RunW RunS)) a

runm :: ProgF -> (Val -> RunM Val) -> RunM Val
runm p k = case p of
  ProgOp (As op) -> do
    lv <- leval op.loc
    v <- ceval op.val
    writelval lv v
    pure v
  ProgOp (Call id args) -> do
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
                vargs = drop (length as') argsval
                venv = Map.fromFoldable $ flip mapWithIndex vargs $ \i va ->
                  Tuple ("vararg-" <> show i) va
              in { name: id, env: Map.union env venv, frid: nxfrid }
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
  ProgOp (Ret e) -> ceval e >>= k
  ProgOp IOW -> output "ciao" *> pure VVoid
  ProgSeq xs -> do
    for_ xs $ \x -> runm x k
    pure VVoid
  ProgWhile e x -> do
    b <- ceval e
    case b of
      VInt 0 -> pure VVoid
      _ -> runm x k *> runm p k
  _ -> pure VVoid

test_reset :: Config
test_reset = Config Nil

test_runm :: Prog -> RWSResult RunS Unit RunW
test_runm prog =
  let r = runExceptT $ runm (ProgOp $ Call "main" Nil) pure
  in runRWS
    (runContT r (\_ -> pure unit))
    (prog <> stdlib)
    { config: test_reset, nxfrid: 0 }

runm2lconfig :: RWSResult RunS Unit RunW -> RunW
runm2lconfig r = let RWSResult s a w = r in w

type State = Int

data Query a
  = Step Int a
  | IsOn (State -> a)

type Input = Unit

data Message = Toggled Boolean

myComp :: forall m. H.Component HH.HTML Query Input Message m
myComp =
  H.component
    { initialState: const initialState
    , render
    , eval
    , receiver: const Nothing
    }
  where

  initialState :: State
  initialState = 0

  render :: State -> H.ComponentHTML Query
  render state =
    let (RunW tr out) = runm2lconfig $ test_runm test_prog_parsed
    in
    HH.div_ $
      [ HH.button [ HE.onClick (HE.input_ $ Step (-1)) ] [ HH.text "<" ]
      , HH.text $ " " <> show state <> " "
      , HH.button [ HE.onClick (HE.input_ $ Step 1) ] [ HH.text ">" ]
      , HH.div_ [ HH.text $ "Out: " <> out ]
      ] <>
      (flip A.mapWithIndex (toUnfoldable tr) $ \i (Config s) ->
        HH.div_ $
          [ HH.text $ "t: " <> show i
          ] <>
          (flip map (toUnfoldable s) $ \fr ->
            HH.div_
              [ HH.text $ "fr [" <> show fr.frid <> "]: " <> fr.name
              , HH.ul_ $ map f (Map.toUnfoldable fr.env)
              ]
          )
      )
    where
    f (Tuple k v) = HH.li_ [ HH.text $ k <> ": " <> show v ]

  eval :: Query ~> H.ComponentDSL State Query Message m
  eval = case _ of
    Step x next -> do
      state <- H.get
      let nextState = state + x
      H.put nextState
      H.raise $ Toggled true
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
