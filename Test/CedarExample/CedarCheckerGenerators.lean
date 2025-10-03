import Test.CedarExample.Cedar
import Plausible.Arbitrary
import Plausible.DeriveArbitrary
import Plausible.Chamelean.GeneratorCombinators
import Plausible.Chamelean.EnumeratorCombinators
import Plausible.Chamelean.ArbitrarySizedSuchThat
import Plausible.Chamelean.DeriveChecker
import Plausible.Chamelean.DeriveConstrainedProducer
import Plausible.Chamelean.DeriveEnum

open Plausible

#check Unit

/-!
This file contains snapshot tests for checkers & generators that
are derived by Chamelean for the inductive relations defined in `Test/CedarExample.Cedar.lean`.

Note: the structure of this file closely follows Mike Hicks's Coq formalization of Cedar (not publicly available),
in particular the order in which he derives checkers/generators using QuickChick.
-/

-- Suppress warnings for unused variables in derived generators/checkers
set_option linter.unusedVariables false

-- Suppress warnings for redundant pattern-match cases in derived generators/checkers
set_option match.ignoreUnusedAlts true

/- We override the default `Arbitrary` instance for `String`s with our custom generator -/
instance : Arbitrary String where
  arbitrary := GeneratorCombinators.elementsWithDefault
    "Aaron" ["Aaron", "John", "Mike", "Kesha", "Hicks", "A", "B", "C", "D"]

instance : Enum String where
  enum := EnumeratorCombinators.oneOfWithDefault
    (pure "Aaron") (pure <$> ["Aaron", "John", "Mike", "Kesha", "Hicks", "A", "B", "C", "D"])

-- Derive `Arbitrary` instances for Cedar data/types/expressions/schemas
deriving instance Arbitrary for
  EntityName, EntityUID, Prim, Var, PatElem, UnaryOp, BinaryOp, CedarExpr,
  Request, BoolType, CedarType, EntitySchemaEntry, ActionSchemaEntry, Schema,
  RequestType, Environment, PathSet

deriving instance Enum for
  EntityName, EntityUID, Prim, Var, PatElem, UnaryOp, BinaryOp, CedarExpr,
  Request, BoolType, CedarType, EntitySchemaEntry, ActionSchemaEntry, Schema,
  RequestType, Environment, PathSet

deriving instance BEq for
  EntityName

deriving instance DecidableEq for PathSet
--------------------------------------------------
-- Checker & Generator for `RecordExpr` relation
--------------------------------------------------

def mul (x y : Nat) := x * y

inductive ExampleB : Nat -> Prop where
| as x y : x = mul x y -> ExampleB (.succ x)
set_option trace.debug true
instance : DecOpt (ExampleB x_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (x_1 : Nat) : Option Bool :=
      (match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun (_ : Unit) =>
            match x_1 with
            | Nat.succ x =>
              EnumeratorCombinators.enumerating Enum.enum
                (fun (y : Nat) => DecOpt.decOpt (Eq  x (mul x y)) initSize) (Min.min 2 initSize)
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun (_ : Unit) =>
            match x_1 with
            | Nat.succ x =>
              EnumeratorCombinators.enumerating Enum.enum
                (fun (y : Nat) => DecOpt.decOpt (Eq x (mul x y)) initSize) (Min.min 2 initSize)
            | _ => Option.some Bool.false,
            ])
    fun size => aux_dec size size x_1

#derive_enumerator (fun (ns : List EntityName) => DefinedEntities ets ns)

#derive_checker (DefinedEntity e n)

#derive_checker (ReqContextToCedarType C t)

#derive_checker (HasTypeVar v x t)

#derive_checker (HasTypePrim v p b)

#derive_checker (DefinedName ns_1_1_1 n)

#derive_checker (WfCedarType ns_1_1 t2)

#derive_checker (WfRecordType ns_1 r)

#derive_checker (BindAttrType ns a t)

#derive_enumerator (fun (TE_1 : CedarType) => HasTypePrim v_1_1_1 P TE_1)

#derive_enumerator (fun (TE_1_1 : CedarType) => ReqContextToCedarType C TE_1_1)

#derive_enumerator (fun (TE_1 : CedarType) => HasTypeVar v_1_1_1 X TE_1)

#derive_checker (LookupEntityAttr FS fb TF)

#derive_enumerator (fun (T_1 : _) => LookupEntityAttr E fnb T_1)

#derive_enumerator (fun (T : _) => GetEntityAttr ets x T)

#derive_checker (GetEntityAttr ets x t_1_1)

#derive_checker (RecordType a)

#derive_checker (SubType a b)

#derive_checker (DefinedEntities ets ns)

instance {α a} [Enum α] [BEq α] : EnumSizedSuchThat α (fun (b : α) => a ≠ b) where
  enumSizedST := fun size size' => LazyList.filter (fun b => a != b) (Enum.enum size)

instance {α a} [Enum α] [BEq α] : EnumSizedSuchThat α (fun (b : α) => b ≠ a) where
  enumSizedST := fun size size' => LazyList.filter (fun b => a != b) (Enum.enum size)

#derive_enumerator (fun (ns_1 : _)=> DefinedName ns_1 n)

#derive_enumerator (fun (n : _)=> DefinedName ns_1 n)

#derive_enumerator (fun (ns : _) => WfCedarType ns t)

#derive_enumerator (fun (t : _) => WfCedarType ns t)

#derive_enumerator (fun (ets : _) => DefinedEntities ets ns)

#derive_enumerator (fun (ns_1 : _) => WfRecordType ns_1 r)

#derive_enumerator (fun (ns : _) => BindAttrType ns a t_1)

#derive_enumerator (fun (t_1 : _) => BindAttrType ns a t_1)

#derive_enumerator (fun (E : _) => LookupEntityAttr E (fn, b) t_1_1)

#derive_enumerator (fun (ets : _) => GetEntityAttr ets a t_1)

#derive_enumerator (fun (R2 : _) => RecordType R2)

#derive_enumerator (fun (TE_1 : _) => SubType T2 TE_1)
#derive_enumerator (fun (T2 : _) => SubType T2 TE_1)

-- #derive_enumerator (fun (t : _) => HasType a b c t)

-- #derive_checker (HasType a b c t)

#check DecOpt.decOpt


-- instance : DecOpt (HasType a_1 v_1 e_1 t_1) where
--   decOpt :=
--     fun size => aux_dec size size a_1 v_1 e_1 t_1
-- instance : EnumSizedSuchThat CedarType (fun TE_1 => HasType a_1_1_1 v_1_1_1 ex_1 TE_1) where
--   enumSizedST :=
--     fun size => aux_enum size size a_1_1_1 v_1_1_1 ex_1
-- #derive_enumerator (fun (TE : CedarType) => HasType a_1_1 v_1_1 ex TE)

instance {α a} [Arbitrary α] [BEq α] : ArbitrarySizedSuchThat α (fun (b : α) => a ≠ b) where
  arbitrarySizedST size := do
    let b <- Arbitrary.arbitrary
    if a == b then
      let b' <- Arbitrary.arbitrary
      if a == b' then
        failure
      else
        return b
    else return b

instance {α a} [Arbitrary α] [BEq α] : ArbitrarySizedSuchThat α (fun (b : α) => b ≠ a) where
  arbitrarySizedST size := do
    let b <- Arbitrary.arbitrary
    if a == b then
      let b' <- Arbitrary.arbitrary
      if a == b' then
        failure
      else
        return b
    else return b

#derive_generator (fun (P : _) => HasTypePrim v_1 P t)
#derive_generator (fun (P : _) => HasTypeVar v_1 P t)

#derive_generator (fun (t : _) => HasTypePrim v_1 P t)

#derive_generator (fun (t_1 : _) => ReqContextToCedarType C t_1)
#derive_generator (fun (t : _) => HasTypeVar v_1 P t)

#derive_generator (fun (ns : _) => DefinedEntities ets ns)

#derive_generator (fun (T_1 : _) => LookupEntityAttr E f T_1)

#derive_generator (fun (T : _) => GetEntityAttr ets t T)

#derive_generator (fun (ns_1 : _) => DefinedName ns_1 n)

#derive_generator (fun (ns : _) => WfCedarType ns n)

#derive_generator (fun (ns_1 : _) => DefinedEntities ns_1 n)

#derive_generator (fun (R2 : _) => RecordType R2)

#derive_generator (fun (t_1 : _) => SubType T2 t_1)

#derive_generator (fun (T2 : _) => SubType T2 t_1)

#derive_generator (fun (n : EntityName) => DefinedName ns_1_1_1 n)

#derive_generator (fun (vfn1_o1_T2_r : _) => WfCedarType ns_1_1 vfn1_o1_T2_r)

#derive_generator (fun (t_1 : _) => BindAttrType ns TE t_1)

/-
error: Invalid pattern: Expected a constructor or constant marked with `[match_pattern]`
---
error: Invalid pattern: Expected a constructor or constant marked with `[match_pattern]`
-/
-- #guard_msgs(error, drop warning) in
-- #derive_generator (fun (t : _) => HasType a v ex t)

#derive_generator (fun (ns_1 : _) => WfRecordType ns_1 r)

#derive_generator (fun (ns : _) => BindAttrType ns TE t_1)

#derive_generator (fun (E : _) => LookupEntityAttr E (fn, b) t_1_1)

#derive_generator (fun (ets : _) => GetEntityAttr ets n t_1)



#derive_generator (fun (r : _) => WfRecordType ns_1 r)

set_option maxHeartbeats 2000000

#derive_generator (fun (vTE_F : _) => BindAttrType ns vTE_F t_1)

-- #derive_generator (fun (ex : (CedarExpr × PathSet)) => HasType a v ex t)

#derive_generator (fun (rs_1_1 : _) => ActionToRequestTypes uid_1 p rs c l_1_1 rs_1_1)

#derive_generator (fun (rs_1 : _) => ActionSchemaEntryToRequestTypes uid a l_1 rs_1)

#derive_generator (fun (rs : _) => ActionSchemaToRequestTypes acts l rs)

#derive_generator (fun (es : _) => SchemaToEnvironments (.MkSchema ets acts) reqs es)
