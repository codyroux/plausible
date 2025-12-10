import Plausible.Gen
open Plausible

/-- Sized generators of type `α` such that `P : α -> Prop` holds for all generated values. -/
class ArbitrarySizedSuchThat (α : Type) (P : α → Prop) where
  arbitrarySizedST : Nat → Gen α

/-- Generators of type `α` such that `P : α -> Prop` holds for all generated values. -/
class ArbitrarySuchThat (α : Type) (P : α → Prop) where
  arbitraryST : Gen α

/-- Every `ArbitrarySizedSuchThat` instance can be automatically given a `ArbitrarySuchThat` instance -/
instance [ArbitrarySizedSuchThat α P] : ArbitrarySuchThat α P where
  arbitraryST := Gen.sized (ArbitrarySizedSuchThat.arbitrarySizedST P)

namespace ArbitrarySizedSuchThat

/-- Prints multiple samples from an `ArbitrarySizedSuchThat` instance.
    Usage: `ArbitrarySizedSuchThat.printSamples (fun n => Even n) 10` -/
def printSamples {α : Type} (P : α → Prop) [Repr α] [ArbitrarySizedSuchThat α P] (size : Nat) (numSamples : Nat := 10) : IO Unit := do
  for _ in [0:numSamples] do
    let sample ← Gen.run (arbitrarySizedST P size) size
    IO.println (repr sample)

end ArbitrarySizedSuchThat

/-- `ArbitrarySizedSuchThat` instance for equality propositions
     where a variable `x` is left-equal to some value `val`.
     (Note: `val` can be the result of a fully-applied function application,
     which is typically how this typeclass is used!) -/
instance {α : Type} [BEq α] {val : α} : ArbitrarySizedSuchThat α (fun x => x = val) where
  arbitrarySizedST _ := return val

/-- `ArbitrarySizedSuchThat` instance for equality propositions
     where a variable `x` is right-equal to some value `val`.
    (Note: `val` can be the result of a fully-applied function application,
     which is typically how this typeclass is used!) -/
instance {α : Type} [BEq α] {val : α} : ArbitrarySizedSuchThat α (fun x => val = x) where
  arbitrarySizedST _ := return val
