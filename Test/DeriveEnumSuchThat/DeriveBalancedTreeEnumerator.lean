
import Plausible.Chamelean.OptionTGen
import Plausible.Chamelean.DecOpt
import Plausible.Chamelean.Enumerators
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.EnumeratorCombinators
import Test.DeriveArbitrarySuchThat.DeriveBalancedTreeGenerator

set_option guard_msgs.diff true

-- #guard_msgs(error, drop warning) in
-- #derive_enumerator (fun (t : BinaryTree) => balancedTree n t)

#print balancedTree

#print instEnumOption

instance : EnumSizedSuchThat BinaryTree (fun t_1 => balancedTree n_1 t_1) where
  enumSizedST :=
    let rec aux_enum (initSize : Nat) (size : Nat) (n_1 : Nat) : OptionT Enumerator BinaryTree :=
      match n_1 with
      | Nat.zero => return BinaryTree.Leaf
      | Nat.succ m =>
        EnumeratorCombinators.enumerate
          [match m with
            | Nat.zero => return BinaryTree.Leaf
            | _ => OptionT.fail,
            do
              let l ← aux_enum initSize size m
              let r ← aux_enum initSize size m
              let x ← OptionT.lift $ @Enum.enum Nat _
              return BinaryTree.Node x l r
           ]
    fun size => aux_enum size size n_1


#eval runSizedEnum (EnumSizedSuchThat.enumSizedST (fun t => balancedTree 3 t)) 10 (limit := 100)
