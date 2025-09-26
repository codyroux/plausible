import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Test.CommonDefinitions.Permutation

#guard_msgs(error) in
#derive_generator (fun (l : List Nat) => Permutation l l')

#guard_msgs(error) in
#derive_generator (fun (l : List Nat) => Permutation l' l)
