import Plausible.Arbitrary
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.DeriveConstrainedProducer
import Test.CommonDefinitions.FunctionCallInConclusion

open Plausible
open DecOpt

set_option guard_msgs.diff true
#print square_of

-- #guard_msgs(error) in
-- #derive_generator (fun (n : Nat) => square_of n m)
