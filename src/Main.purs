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
import Control.Monad.RWS (RWS, tell, ask, get, put, runRWS, RWSResult(..))
import Control.Monad.Cont (ContT, callCC, runContT)
import Control.Monad.Trans.Class (lift)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
-- import Halogen.HTML.Properties as HP
import Halogen.Aff as HA
import Halogen.VDom.Driver (runUI)

data Op =
    As { id :: String , val :: Expr }
  | Call String (L.List Int)
  | Ret Expr
  | IOW String (L.List Int)
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
  | EConst Int
  | ECall String (L.List Expr)
  | EBinop PrimopBin Expr Expr
  | EUnop PrimopUn Expr
  | ETernop Expr Expr Expr

type Frame = { name :: String, env :: Map.Map String Int }

data Config = Config (NL.NonEmptyList Frame)

ceval :: Expr -> RunM Int
ceval e = case e of
  EId id -> do
    Config c <- lift get
    pure $ fromMaybe 0 $ Map.lookup id (NL.head c).env
  EConst k -> pure k
  ECall id args -> do
    avs <- for args ceval
    runm (ProgOp $ Call id avs) pure
  EBinop op a b -> do
    av <- ceval a
    bv <- ceval b
    pure $ (primopBin op) av bv
  EUnop _ _ -> pure 0
  ETernop _ _ _ -> pure 0

data ProgF =
    ProgOp Op
  | ProgSeq (L.List ProgF)
  | ProgWhile Expr ProgF
  | ProgIf Expr ProgF
  | ProgIfElse Expr ProgF ProgF

type Prog = L.List { fname :: String, argns :: L.List String, code :: ProgF }

test_prog_main :: ProgF
test_prog_main = ProgSeq $ L.fromFoldable
  [ ProgOp $ As { id: "i", val: EConst 0 }
  , ProgOp $ As { id: "x", val: EConst 0 }
  , ProgWhile (EBinop PoLT (EId "i") (EConst 5)) $ ProgSeq $ L.fromFoldable
    [ ProgOp $ As { id: "x", val: EBinop PoAdd (EId "x") (EId "i") }
    , ProgOp $ As { id: "i", val: EBinop PoAdd (EId "i") (EConst 1) }
    ]
  , ProgOp $ As { id: "a", val: ECall "foo" $
      L.fromFoldable [EBinop PoAdd (EId "x") (EConst 1)] }
  , ProgOp $ Ret $ EConst 0
  ]

test_prog_foo :: ProgF
test_prog_foo = ProgSeq $ L.fromFoldable
  [ ProgOp $ As { id: "i", val: EBinop PoAdd (EId "i") (EConst 6) }
  , ProgOp $ Ret $ EBinop PoAdd (EId "i") (EConst 2)
  , ProgOp $ As { id: "i", val: EConst 4 }
  ]

test_prog :: Prog
test_prog = L.fromFoldable
  [ { fname: "main", argns: L.Nil, code: test_prog_main }
  , { fname: "foo", argns: L.fromFoldable ["i"], code: test_prog_foo }
  ]

type RunM a = ContT Int (RWS Prog (L.List Config) Config) a

runm :: ProgF -> (Int -> RunM Int) -> RunM Int
runm p k = case p of
  ProgOp (As op) -> do
    Config c <- lift $ get
    v <- ceval op.val
    let
      top = NL.head c
      rest = NL.tail c
      c2 = top { env = Map.insert op.id v top.env }
      y = Config $ NL.NonEmptyList $ NonEmpty c2 rest
    lift $ tell $ L.singleton y
    lift $ put y
    pure v
  ProgOp (Call id args) -> do
    prog <- lift ask
    let prog_fs = flip map prog $ \{fname: f, argns: as, code: c} -> T.Tuple f (T.Tuple as c)
    case T.lookup id prog_fs of
      Just (T.Tuple as f) -> do
        Config c <- lift get
        let
          fr = { name: id, env: Map.fromFoldable $ L.zip as args }
          y = Config $ NL.NonEmptyList $ NonEmpty fr (NL.toList c)
        lift $ tell $ L.singleton y
        lift $ put y
        v <- callCC $ runm f
        lift $ put $ Config c
        lift $ get >>= (tell <<< L.singleton)
        pure v
      Nothing -> pure 0 -- should be unreachable (func name not in prog)
  ProgOp (Ret e) -> ceval e >>= k
  ProgSeq xs -> do
    F.for_ xs $ \x -> runm x k
    pure 0
  ProgWhile e x -> do
    b <- ceval e
    case b of
      0 -> pure 0
      _ -> runm x k *> runm p k
  _ -> pure 0

test_reset :: Config
test_reset = Config $ NL.singleton { name: "Bot", env: Map.empty }

test_runm :: Prog -> RWSResult Config Int (L.List Config)
test_runm prog =
  let r = runm (ProgOp $ Call "main" L.Nil) pure
  in runRWS (runContT r pure) prog test_reset

runm2lconfig :: RWSResult Config Int (L.List Config) -> L.List Config
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
              [ HH.text $ "fr: " <> fr.name
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
