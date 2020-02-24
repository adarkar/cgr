module Main where

import Prelude
import Effect (Effect)
import Effect.Console (log)
import Data.Map as Map
-- import Data.Array
import Data.Maybe (Maybe(..))
import Data.Tuple as T
-- import Data.Unfoldable
import Halogen as H
import Halogen.HTML as HH
-- import Halogen.HTML.Events as HE
-- import Halogen.HTML.Properties as HP
import Halogen.Aff as HA
import Halogen.VDom.Driver (runUI)

data Op =
  As { id :: String , val :: Int }

data Config =
  Config { env :: Map.Map String Int }

type State = Config

data Query a
  = Toggle a
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
  initialState = Config { env: Map.singleton "x" 42 }

  render :: State -> H.ComponentHTML Query
  render state =
    let (Config st) = state
        s = st.env
    in
    HH.ul_ $ map f (Map.toUnfoldable s)
    where
    f (T.Tuple k v) = HH.li_ [ HH.text $ k <> ": " <> show v ]

  eval :: Query ~> H.ComponentDSL State Query Message m
  eval = case _ of
    Toggle next -> do
      state <- H.get
      let nextState = state
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
