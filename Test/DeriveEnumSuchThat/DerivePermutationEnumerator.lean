import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.EnumeratorCombinators
import Test.CommonDefinitions.Permutation


#guard_msgs(error) in
#derive_enumerator (fun (l : List Nat) => Permutation l l')

#guard_msgs(error) in
#derive_enumerator (fun (l : List Nat) => Permutation l' l)
