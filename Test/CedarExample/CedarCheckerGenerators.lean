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
--------------------------------------------------
-- Checker & Generator for `RecordExpr` relation
--------------------------------------------------

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
#print EnumSuchThat
#print Enumerator
instance {α a} [Enum α] [BEq α] : EnumSizedSuchThat α (fun (b : α) => a ≠ b) where
  enumSizedST := fun size size' => LazyList.filter (fun b => a != b) (Enum.enum size)

#derive_enumerator (fun (ns_1 : _)=> DefinedName ns_1 n)

#derive_enumerator (fun (ns : _) => WfCedarType ns t)

#derive_enumerator (fun (ets : _) => DefinedEntities ets ns)

#derive_enumerator (fun (ns_1 : _) => WfRecordType ns_1 r)

#derive_enumerator (fun (ns : _) => BindAttrType ns a t_1)

#derive_enumerator (fun (E : _) => LookupEntityAttr E (fn, b) t_1_1)

#derive_enumerator (fun (ets : _) => GetEntityAttr ets a t_1)

#check DecOpt.decOpt

#derive_checker (HasType a v e t)





#derive_enumerator (fun (TE : CedarType) => HasType a_1_1 v_1_1 ex TE)



#derive_generator (fun (ex : (CedarExpr × PathSet)) => HasType a v ex t)
