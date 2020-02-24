module Main where

import Prelude
import Effect (Effect)
import Effect.Console (log)
import Data.List as L
import Data.Map as Map
-- import Data.Array
import Data.Maybe (Maybe(..))
import Data.Tuple as T
-- import Data.Unfoldable
-- import Data.Foldable
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
-- import Halogen.HTML.Properties as HP
import Halogen.Aff as HA
import Halogen.VDom.Driver (runUI)

data Op =
  As { id :: String , val :: Int }

data Config =
  Config { env :: Map.Map String Int }

type Prog = L.List Op

type Run = { reset :: Config, run :: L.List (T.Tuple Op Config) }

run :: Prog -> Config -> Run
run p (Config reset) = { reset: Config reset, run: go reset p }
  where
  go c L.Nil = L.Nil
  go c (L.Cons x xs) =
    let c2 = step x c
    in L.Cons (T.Tuple x (Config c2)) (go c2 xs)
  step (As op) c = { env: Map.insert op.id op.val c.env }

test_prog :: Prog
test_prog = L.fromFoldable
  [ As { id: "i", val: 0 }
  , As { id: "x", val: 0 }
  , As { id: "i", val: 1 }
  , As { id: "x", val: 1 }
  , As { id: "i", val: 2 }
  , As { id: "x", val: 3 }
  ]

test_reset :: Config
test_reset = Config { env: Map.empty }

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
  initialState = (-1)

  render :: State -> H.ComponentHTML Query
  render state =
    let (Config s) = case test_run.run L.!! state of
            Just s -> T.snd s
            Nothing -> test_run.reset
    in
    HH.div_
      [ HH.button [ HE.onClick (HE.input_ $ Step (-1)) ] [ HH.text "<" ]
      , HH.button [ HE.onClick (HE.input_ $ Step 1) ] [ HH.text ">" ]
      , HH.ul_ $ map f (Map.toUnfoldable s.env)
      ]
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
