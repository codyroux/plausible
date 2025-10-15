import Plausible.Chamelean.DeriveConstrainedProducer

structure TypeBox where
  ty : Type

instance : Inhabited TypeBox := ⟨⟨Unit⟩⟩

abbrev NatFoo : TypeBox where
  ty := Nat

opaque SomeFoo : TypeBox

def five := 5

inductive TypeBoxPred : Nat → Prop where
| someRefl {x : NatFoo.ty} : x = x → TypeBoxPred 5

inductive TypeBoxPredS : String → Prop where
| someRefl {x : NatFoo.ty} : x = x → TypeBoxPredS "lol"

inductive TypeBoxPred' : Nat → Prop where
| someRefl {x : SomeFoo.ty} : x = x → TypeBoxPred' five

#guard_msgs(error, drop info, drop warning) in
#derive_generator (fun (n : Nat) => TypeBoxPred n)

#guard_msgs(error, drop info, drop warning) in
#derive_generator (fun (n : _) => TypeBoxPredS n)

#guard_msgs(drop error, drop warning, drop info) in
#derive_generator (fun (n : Nat) => TypeBoxPred' n)
