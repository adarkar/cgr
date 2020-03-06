module Main where

import Prelude
import Effect (Effect)
import Effect.Console (log)
import Data.Maybe (fromMaybe, Maybe(..))
import Data.List as L
import Data.List.NonEmpty as NL
import Data.NonEmpty (NonEmpty(..))
import Data.Map as Map
import Data.Array as A
import Data.Tuple as T
-- import Data.Unfoldable
import Data.Foldable as F
import Data.Traversable (for)
import Control.Monad.RWS (RWS, tell, ask, get, gets, put, modify_, runRWS, RWSResult(..))
import Control.Monad.Cont (ContT, callCC, runContT)
import Control.Monad.Trans.Class (lift)
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
  | VRef Int String -- to a frame: int fr index, string var name

instance showVal :: Show Val where
  show VVoid = "void"
  show (VInt x) = show x
  show (VArray x) = show x
  show _ = "todo"

data LVal =
   LVId String
 | LVSubscr String Expr

data Op =
    As { lv :: LVal, val :: Expr }
  | Call String (L.List Val)
  | Ret Expr
  | IOW
  | IOR String (L.List Int)

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
  | ECall String (L.List Expr)
  | EBinop PrimopBin Expr Expr
  | EUnop PrimopUn Expr
  | ETernop Expr Expr Expr

type Frame = { name :: String, env :: Map.Map String Val, frid :: Int }

data Config = Config (NL.NonEmptyList Frame)

ceval :: Expr -> RunM Val
ceval e = case e of
  EId id -> do
    Config c <- lift $ gets _.config
    pure $ fromMaybe VVoid $ Map.lookup id (NL.head c).env
  EConst k -> pure k
  ECall id args -> do
    avs <- for args ceval
    runm (ProgOp $ Call id avs) pure
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

data ProgF =
    ProgOp Op
  | ProgSeq (L.List ProgF)
  | ProgWhile Expr ProgF
  | ProgIf Expr ProgF
  | ProgIfElse Expr ProgF ProgF

data Argdef =
    Argdef (L.List String)
  | Argvar (L.List String)

type Prog = L.List { fname :: String, argns :: Argdef, code :: ProgF }

test_prog_main :: ProgF
test_prog_main = ProgSeq $ L.fromFoldable
  [ ProgOp $ As { lv: LVId "i", val: EConst $ VInt 0 }
  , ProgOp $ As { lv: LVId "x", val: EConst $ VInt 0 }
  , ProgWhile (EBinop PoLT (EId "i") (EConst $ VInt 5)) $ ProgSeq $ L.fromFoldable
    [ ProgOp $ As { lv: LVId "x", val: EBinop PoAdd (EId "x") (EId "i") }
    , ProgOp $ As { lv: LVId "i", val: EBinop PoAdd (EId "i") (EConst $ VInt 1) }
    ]
  , ProgOp $ As { lv: LVId "a", val: ECall "foo" $
      L.fromFoldable [EBinop PoAdd (EId "x") (EConst $ VInt 1)] }
  , ProgOp $ Call "printf" $ L.fromFoldable $ map VInt [0,1,2]
  , ProgOp $ As { lv: LVId "ar", val: EConst $ VArray $ map VInt [1,2,3,5,8] }
  , ProgOp $ As { lv: LVSubscr "ar" (EConst $ VInt 1), val: EConst $ VInt 0 }
  , ProgOp $ Ret $ EConst $ VInt 0
  ]

test_prog_foo :: ProgF
test_prog_foo = ProgSeq $ L.fromFoldable
  [ ProgOp $ As { lv: LVId "i", val: EBinop PoAdd (EId "i") (EConst $ VInt 6) }
  , ProgOp $ Ret $ EBinop PoAdd (EId "i") (EConst $ VInt 2)
  , ProgOp $ As { lv: LVId "i", val: EConst $ VInt 4 }
  ]

test_prog :: Prog
test_prog = L.fromFoldable
  [ { fname: "main", argns: Argdef L.Nil, code: test_prog_main }
  , { fname: "foo", argns: Argdef $ L.fromFoldable ["i"], code: test_prog_foo }
  ]

stdlib_printf :: ProgF
stdlib_printf = ProgOp IOW

stdlib :: Prog
stdlib = L.fromFoldable
  [ { fname: "printf", argns: Argvar $ L.fromFoldable ["format"], code: stdlib_printf }
  ]

type RunS = { config :: Config, nxfrid :: Int }

type RunM a = ContT Unit (RWS Prog (L.List Config) RunS) a

runm :: ProgF -> (Val -> RunM Val) -> RunM Val
runm p k = case p of
  ProgOp (As op) -> do
    Config c <- lift $ gets _.config
    v <- ceval op.val
    let
      top = NL.head c
      rest = NL.tail c
    env' <- case op.lv of
      LVId id -> pure $ Map.insert id v top.env
      LVSubscr id ix -> do
        ixv <- ceval ix
        case ixv of
          VInt ixvi ->
            pure $ Map.update up id top.env
            where
              up ary = case ary of
                VArray ary' -> VArray <$> A.updateAt ixvi v ary'
                _ -> Nothing
          _ -> pure top.env
    let
      c2 = top { env = env' }
      y = Config $ NL.NonEmptyList $ NonEmpty c2 rest
    lift $ tell $ L.singleton y
    lift $ modify_ $ _{ config = y }
    pure v
  ProgOp (Call id args) -> do
    prog <- lift ask
    let prog_fs = flip map prog $ \{fname: f, argns: as, code: c} -> T.Tuple f (T.Tuple as c)
    case T.lookup id prog_fs of
      Just (T.Tuple as f) -> do
        { config: Config c, nxfrid: nxfrid } <- lift get
        let
          fr = case as of
            Argdef as' -> { name: id, env: Map.fromFoldable $ L.zip as' args, frid: nxfrid }
            Argvar as' ->
              let
                env = Map.fromFoldable $ L.zip as' args
                vargs = L.drop (L.length as') args
                venv = Map.fromFoldable $ flip L.mapWithIndex vargs $ \i va ->
                  T.Tuple ("vararg-" <> show i) va
              in { name: id, env: Map.union env venv, frid: nxfrid }
          y = Config $ NL.NonEmptyList $ NonEmpty fr (NL.toList c)
        lift $ tell $ L.singleton y
        lift $ put { config: y, nxfrid: nxfrid + 1 }
        v <- callCC $ runm f
        lift $ modify_ $ _{ config = Config c }
        lift $ gets _.config >>= (tell <<< L.singleton)
        pure v
      Nothing -> pure VVoid -- should be unreachable (func name not in prog)
  ProgOp (Ret e) -> ceval e >>= k
  ProgSeq xs -> do
    F.for_ xs $ \x -> runm x k
    pure VVoid
  ProgWhile e x -> do
    b <- ceval e
    case b of
      VInt 0 -> pure VVoid
      _ -> runm x k *> runm p k
  _ -> pure VVoid

test_reset :: Config
test_reset = Config $ NL.singleton { name: "Bot", env: Map.empty, frid: 0 }

test_runm :: Prog -> RWSResult RunS Unit (L.List Config)
test_runm prog =
  let r = runm (ProgOp $ Call "main" L.Nil) pure
  in runRWS (runContT r (\_ -> pure unit)) (prog <> stdlib) { config: test_reset, nxfrid: 1 }

runm2lconfig :: RWSResult RunS Unit (L.List Config) -> L.List Config
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
    let cs = runm2lconfig $ test_runm test_prog
    in
    HH.div_ $
      [ HH.button [ HE.onClick (HE.input_ $ Step (-1)) ] [ HH.text "<" ]
      , HH.text $ " " <> show state <> " "
      , HH.button [ HE.onClick (HE.input_ $ Step 1) ] [ HH.text ">" ]
      ] <>
      (flip A.mapWithIndex (L.toUnfoldable cs) $ \i (Config s) ->
        HH.div_ $
          [ HH.text $ "t: " <> show i
          ] <>
          (flip map (NL.toUnfoldable s) $ \fr ->
            HH.div_
              [ HH.text $ "fr [" <> show fr.frid <> "]: " <> fr.name
              , HH.ul_ $ map f (Map.toUnfoldable fr.env)
              ]
          )
      )
    where
    f (T.Tuple k v) = HH.li_ [ HH.text $ k <> ": " <> show v ]

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
  log <<< show $ L.length $ runm2lconfig $ test_runm test_prog
  HA.runHalogenAff do
    body <- HA.awaitBody
    runUI myComp unit body
