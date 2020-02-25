module Main where

import Prelude
import Effect (Effect)
import Effect.Console (log)
import Data.Maybe (fromMaybe, Maybe(..))
import Data.List as L
import Data.List.NonEmpty as NL
import Data.NonEmpty (NonEmpty(..))
import Data.Map as Map
-- import Data.Array
import Data.Tuple as T
-- import Data.Unfoldable
-- import Data.Foldable
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
-- import Halogen.HTML.Properties as HP
import Halogen.Aff as HA
import Halogen.VDom.Driver (runUI)

data Val =
    VI Int
  | VE Expr

data Op =
  As { id :: String , val :: Val }

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
  | EBinop PrimopBin Expr Expr
  | EUnop PrimopUn Expr
  | ETernop Expr Expr Expr

type Env = { env :: Map.Map String Int }

data Config =
  Config (NL.NonEmptyList Env)

ceval :: Expr -> Config -> Int
ceval e (Config c) = case e of
  EId id -> fromMaybe 0 $ Map.lookup id (NL.head c).env
  EConst k -> k
  EBinop op a b -> (primopBin op) (ceval a $ Config c) (ceval b $ Config c)
  EUnop _ _ -> 0
  ETernop _ _ _ -> 0

data Prog =
    ProgOp Op
  | ProgSeq (L.List Prog)
  | ProgWhile Expr Prog
  | ProgIf Expr Prog
  | ProgIfElse Expr Prog Prog

type Run = { reset :: Config, run :: L.List (T.Tuple Op Config) }

run :: Prog -> Config -> Run
run p (Config reset) = { reset: Config reset, run: go reset p }
  where
  go c (ProgOp (As op)) =
    let
      v = case op.val of
        VI i -> i
        VE e -> ceval e (Config c)
      top = NL.head c
      rest = NL.tail c
      c2 = { env: Map.insert op.id v top.env }
    in L.singleton $ T.Tuple (As $ op { val = VI v }) (Config $ NL.NonEmptyList $ NonEmpty c2 rest)
  go c (ProgSeq L.Nil) = L.Nil
  go c (ProgSeq (L.Cons x xs)) =
    let
      seq = go c x
      (Config c2) = fromMaybe (Config c) <<< map T.snd <<< L.last $ seq
      rest = go c2 $ ProgSeq xs
    in seq <> rest
  go c w@(ProgWhile e x) =
    case ceval e (Config c) of
      0 -> L.Nil
      _ ->
        let
          seq = go c x
          (Config c2) = fromMaybe (Config c) <<< map T.snd <<< L.last $ seq
          rest = go c2 w
        in seq <> rest
  go c _ = L.Nil

test_prog :: Prog
test_prog = ProgSeq $ L.fromFoldable
  [ ProgOp $ As { id: "i", val: VI 0 }
  , ProgOp $ As { id: "x", val: VI 0 }
  , ProgWhile (EBinop PoLT (EId "i") (EConst 5)) $ ProgSeq $ L.fromFoldable
    [ ProgOp $ As { id: "x", val: VE $ EBinop PoAdd (EId "x") (EId "i") }
    , ProgOp $ As { id: "i", val: VE $ EBinop PoAdd (EId "i") (EConst 1) }
    ]
  ]

test_reset :: Config
test_reset = Config $ NL.singleton { env: Map.empty }

test_run :: Run
test_run = run test_prog test_reset

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
    let (Config s) = case test_run.run L.!! (state-1) of
            Just s -> T.snd s
            Nothing -> test_run.reset
    in
    HH.div_ $
      [ HH.button [ HE.onClick (HE.input_ $ Step (-1)) ] [ HH.text "<" ]
      , HH.text $ " " <> show state <> " "
      , HH.button [ HE.onClick (HE.input_ $ Step 1) ] [ HH.text ">" ]
      ] <>
      (NL.toUnfoldable $ map (\fr ->
        HH.div_
          [ HH.text "frame"
          , HH.ul_ $ map f (Map.toUnfoldable fr.env)
          ])
        s)
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
  log <<< show $ L.length test_run.run
  HA.runHalogenAff do
    body <- HA.awaitBody
    runUI myComp unit body
