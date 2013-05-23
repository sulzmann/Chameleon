--------------------------------------------------------------------------------
--
-- The Scheme Back-end.
--
--------------------------------------------------------------------------------

module Backends.Scheme.Generate (
    generate
) where

import qualified Backends.Scheme.GenerateLazy

generate = Backends.Scheme.GenerateLazy.generate
