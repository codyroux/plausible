
import Plausible.Arbitrary
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Gen

set_option guard_msgs.diff true

mutual
  inductive Even : Nat → Prop where
    | zero_is_even : Even .zero
    | succ_of_odd_is_even : ∀ n : Nat, Odd n → Even (.succ n)

  inductive Odd : Nat → Prop where
    | succ_of_even_is_odd : ∀ n : Nat, Even n → Odd (.succ n)
end

/-- To make the derived generators below compile, we need to
    manually add a dummy instance of `ArbitrarySizedSuchThat` for one of the relations, since Lean doesn't support
    mutually recursively typeclass instances currently.

    Note that the instance of `ArbitrarySizedSuchThat` for `Odd` below (produced by `#derive_generator`)
    will shadow this one -- it takes precedence over this dummy instance.


    Note from Segev: This does not work, it remembers the old instance from when it was defined. -/
instance : ArbitrarySizedSuchThat Nat (fun n => Odd n) where
  arbitrarySizedST (_ : Nat) := return 1

instance : ArbitrarySizedSuchThat Nat (fun n => Even n) where
  arbitrarySizedST (_ : Nat) := ArbitrarySizedSuchThat.arbitrarySizedST (fun n => Odd n) 1

#eval Plausible.Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST (fun n => Even n) 1) 0

instance : ArbitrarySizedSuchThat Nat (fun n => Odd n) where
  arbitrarySizedST (_ : Nat) := return 2

#eval Plausible.Gen.run (ArbitrarySizedSuchThat.arbitrarySizedST (fun n => Even n) 1) 0

#guard_msgs(error) in
#derive_generator (fun (n : Nat) => Even n)

#guard_msgs(error) in
#derive_generator (fun (n : Nat) => Odd n)
