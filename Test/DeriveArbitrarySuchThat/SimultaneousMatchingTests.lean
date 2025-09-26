import Plausible.Gen
import Plausible.Chamelean.OptionTGen
import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.DeriveChecker
import Test.CommonDefinitions.ListRelations
import Test.DeriveDecOpt.SimultaneousMatchingTests

open Plausible
open ArbitrarySizedSuchThat OptionTGen

set_option guard_msgs.diff true


#guard_msgs(error) in
#derive_generator (fun (l : List Nat) => InList x l)


#guard_msgs(error) in
#derive_generator (fun (l: List Nat) => MinOk l a)

#guard_msgs(error) in
#derive_generator (fun (l : List Nat) => MinEx n l l')

#guard_msgs(error) in
#derive_generator (fun (l : List Nat) => MinEx3 x l l')

#guard_msgs(error) in
#derive_generator (fun (l' : List Nat) => MinEx2 x l l')

#guard_msgs(error) in
#derive_generator (fun (l : List Nat) => MinEx2 x l l')
