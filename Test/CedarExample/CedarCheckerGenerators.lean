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

instance : DecOpt (HasType a_1 b_1 c_1 t_1) where
  decOpt :=
    let rec aux_dec (initSize : Nat) (size : Nat) (a_1 : PathSet) (b_1 : Environment) (c_1 : CedarExpr × PathSet)
      (t_1 : CedarType) : Option Bool :=
      (match size with
      | Nat.zero =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match t_1 with
            | CedarType.boolType (BoolType.ff) =>
              match c_1 with
              | Prod.mk (CedarExpr.lit P) (PathSet.allpaths) =>
                DecOpt.andOptList
                  [DecOpt.decOpt (HasTypePrim b_1 P (CedarType.boolType (BoolType.ff))) initSize,
                    DecOpt.decOpt (HasTypePrim b_1 P (CedarType.boolType (BoolType.ff))) initSize]
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match c_1 with
            | Prod.mk (CedarExpr.lit P) (PathSet.somepaths (List.nil)) =>
              DecOpt.andOptList
                [DecOpt.decOpt (HasTypePrim b_1 P t_1) initSize,
                  DecOpt.andOptList
                    [DecOpt.decOpt (Ne t_1 (CedarType.boolType (BoolType.ff))) initSize,
                      DecOpt.andOptList
                        [DecOpt.decOpt (HasTypePrim b_1 P t_1) initSize,
                          DecOpt.decOpt (Ne t_1 (CedarType.boolType (BoolType.ff))) initSize]]]
            | _ => Option.some Bool.false,
            fun _ =>
            match c_1 with
            | Prod.mk (CedarExpr.var X) (PathSet.somepaths (List.nil)) =>
              DecOpt.andOptList
                [DecOpt.decOpt (HasTypeVar b_1 X t_1) initSize, DecOpt.decOpt (HasTypeVar b_1 X t_1) initSize]
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | CedarType.boolType (BoolType.tt) =>
              match c_1 with
              |
              Prod.mk (CedarExpr.binaryApp (BinaryOp.equals) (CedarExpr.lit P) (CedarExpr.lit u_4))
                  (PathSet.somepaths (List.nil)) =>
                DecOpt.decOpt (BEq.beq u_4 P) initSize
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | CedarType.boolType (BoolType.ff) =>
              match c_1 with
              |
              Prod.mk (CedarExpr.binaryApp (BinaryOp.equals) (CedarExpr.lit P1) (CedarExpr.lit P2))
                  (PathSet.allpaths) =>
                DecOpt.andOptList [DecOpt.decOpt (Ne P1 P2) initSize, DecOpt.decOpt (Ne P1 P2) initSize]
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | CedarType.recordTypeNil =>
              match c_1 with
              | Prod.mk (CedarExpr.recExprNil) (PathSet.somepaths (List.nil)) => Option.some Bool.true
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false]
      | Nat.succ size' =>
        DecOpt.checkerBacktrack
          [fun _ =>
            match t_1 with
            | CedarType.boolType (BoolType.ff) =>
              match c_1 with
              | Prod.mk (CedarExpr.lit P) (PathSet.allpaths) =>
                DecOpt.andOptList
                  [DecOpt.decOpt (HasTypePrim b_1 P (CedarType.boolType (BoolType.ff))) initSize,
                    DecOpt.decOpt (HasTypePrim b_1 P (CedarType.boolType (BoolType.ff))) initSize]
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match c_1 with
            | Prod.mk (CedarExpr.lit P) (PathSet.somepaths (List.nil)) =>
              DecOpt.andOptList
                [DecOpt.decOpt (HasTypePrim b_1 P t_1) initSize,
                  DecOpt.andOptList
                    [DecOpt.decOpt (Ne t_1 (CedarType.boolType (BoolType.ff))) initSize,
                      DecOpt.andOptList
                        [DecOpt.decOpt (HasTypePrim b_1 P t_1) initSize,
                          DecOpt.decOpt (Ne t_1 (CedarType.boolType (BoolType.ff))) initSize]]]
            | _ => Option.some Bool.false,
            fun _ =>
            match c_1 with
            | Prod.mk (CedarExpr.var X) (PathSet.somepaths (List.nil)) =>
              DecOpt.andOptList
                [DecOpt.decOpt (HasTypeVar b_1 X t_1) initSize, DecOpt.decOpt (HasTypeVar b_1 X t_1) initSize]
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | CedarType.boolType (BoolType.tt) =>
              match c_1 with
              |
              Prod.mk (CedarExpr.binaryApp (BinaryOp.equals) (CedarExpr.lit P) (CedarExpr.lit u_4))
                  (PathSet.somepaths (List.nil)) =>
                DecOpt.decOpt (BEq.beq u_4 P) initSize
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | CedarType.boolType (BoolType.ff) =>
              match c_1 with
              |
              Prod.mk (CedarExpr.binaryApp (BinaryOp.equals) (CedarExpr.lit P1) (CedarExpr.lit P2))
                  (PathSet.allpaths) =>
                DecOpt.andOptList [DecOpt.decOpt (Ne P1 P2) initSize, DecOpt.decOpt (Ne P1 P2) initSize]
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | CedarType.recordTypeNil =>
              match c_1 with
              | Prod.mk (CedarExpr.recExprNil) (PathSet.somepaths (List.nil)) => Option.some Bool.true
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
        
            fun _ =>
            match c_1 with
            | Prod.mk (CedarExpr.ite E1 E2 E3) x3 =>
              DecOpt.andOptList
                [aux_dec initSize size' a_1 b_1 (Prod.mk E3 x3) t_1,
                  EnumeratorCombinators.enumerating Enum.enum
                    (fun x1 =>
                      DecOpt.andOptList
                        [aux_dec initSize size' a_1 b_1 (Prod.mk E3 x3) t_1,
                          aux_dec initSize size' a_1 b_1 (Prod.mk E1 x1) (CedarType.boolType (BoolType.ff))])
                    (min 2 initSize)]
            | _ => Option.some Bool.false,
            fun _ =>
            match c_1 with
            | Prod.mk (CedarExpr.andExpr E1 E2) x =>
              DecOpt.andOptList
                [aux_dec initSize size' a_1 b_1
                    (Prod.mk (CedarExpr.ite E1 E2 (CedarExpr.lit (Prim.boolean (Bool.false)))) x) t_1,
                  aux_dec initSize size' a_1 b_1
                    (Prod.mk (CedarExpr.ite E1 E2 (CedarExpr.lit (Prim.boolean (Bool.false)))) x) t_1]
            | _ => Option.some Bool.false,
            fun _ =>
            match c_1 with
            | Prod.mk (CedarExpr.orExpr E1 E2) x =>
              DecOpt.andOptList
                [aux_dec initSize size' a_1 b_1
                    (Prod.mk (CedarExpr.ite E1 (CedarExpr.lit (Prim.boolean (Bool.true))) E2) x) t_1,
                  aux_dec initSize size' a_1 b_1
                    (Prod.mk (CedarExpr.ite E1 (CedarExpr.lit (Prim.boolean (Bool.true))) E2) x) t_1]
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | CedarType.boolType (BoolType.anyBool) =>
              match c_1 with
              | Prod.mk (CedarExpr.unaryApp (UnaryOp.not) e) (PathSet.somepaths (List.nil)) =>
                EnumeratorCombinators.enumerating Enum.enum
                  (fun x => aux_dec initSize size' a_1 b_1 (Prod.mk e x) (CedarType.boolType (BoolType.anyBool)))
                  (min 2 initSize)
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | CedarType.boolType (BoolType.ff) =>
              match c_1 with
              | Prod.mk (CedarExpr.unaryApp (UnaryOp.not) e) (PathSet.allpaths) =>
                EnumeratorCombinators.enumerating Enum.enum
                  (fun x => aux_dec initSize size' a_1 b_1 (Prod.mk e x) (CedarType.boolType (BoolType.tt)))
                  (min 2 initSize)
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | CedarType.boolType (BoolType.tt) =>
              match c_1 with
              | Prod.mk (CedarExpr.unaryApp (UnaryOp.not) e) (PathSet.somepaths (List.nil)) =>
                EnumeratorCombinators.enumerating Enum.enum
                  (fun x => aux_dec initSize size' a_1 b_1 (Prod.mk e x) (CedarType.boolType (BoolType.ff)))
                  (min 2 initSize)
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | CedarType.intType =>
              match c_1 with
              | Prod.mk (CedarExpr.unaryApp (UnaryOp.neg) e) (PathSet.somepaths (List.nil)) =>
                EnumeratorCombinators.enumerating Enum.enum
                  (fun x => aux_dec initSize size' a_1 b_1 (Prod.mk e x) (CedarType.intType)) (min 2 initSize)
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | CedarType.boolType (BoolType.anyBool) =>
              match c_1 with
              | Prod.mk (CedarExpr.unaryApp (UnaryOp.like P) e) (PathSet.somepaths (List.nil)) =>
                EnumeratorCombinators.enumerating Enum.enum
                  (fun x => aux_dec initSize size' a_1 b_1 (Prod.mk e x) (CedarType.stringType)) (min 2 initSize)
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | CedarType.boolType (BoolType.anyBool) =>
              match c_1 with
              | Prod.mk (CedarExpr.binaryApp (BinaryOp.less) E1 E2) (PathSet.somepaths (List.nil)) =>
                EnumeratorCombinators.enumerating Enum.enum
                  (fun x1 =>
                    DecOpt.andOptList
                      [aux_dec initSize size' a_1 b_1 (Prod.mk E1 x1) (CedarType.intType),
                        EnumeratorCombinators.enumerating Enum.enum
                          (fun x2 => aux_dec initSize size' a_1 b_1 (Prod.mk E2 x2) (CedarType.intType))
                          (min 2 initSize)])
                  (min 2 initSize)
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | CedarType.boolType (BoolType.anyBool) =>
              match c_1 with
              | Prod.mk (CedarExpr.binaryApp (BinaryOp.lessEq) E1 E2) (PathSet.somepaths (List.nil)) =>
                EnumeratorCombinators.enumerating Enum.enum
                  (fun x1 =>
                    DecOpt.andOptList
                      [aux_dec initSize size' a_1 b_1 (Prod.mk E1 x1) (CedarType.intType),
                        EnumeratorCombinators.enumerating Enum.enum
                          (fun x2 => aux_dec initSize size' a_1 b_1 (Prod.mk E2 x2) (CedarType.intType))
                          (min 2 initSize)])
                  (min 2 initSize)
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | CedarType.intType =>
              match c_1 with
              | Prod.mk (CedarExpr.binaryApp (BinaryOp.add) E1 E2) (PathSet.somepaths (List.nil)) =>
                EnumeratorCombinators.enumerating Enum.enum
                  (fun x1 =>
                    DecOpt.andOptList
                      [aux_dec initSize size' a_1 b_1 (Prod.mk E1 x1) (CedarType.intType),
                        EnumeratorCombinators.enumerating Enum.enum
                          (fun x2 => aux_dec initSize size' a_1 b_1 (Prod.mk E2 x2) (CedarType.intType))
                          (min 2 initSize)])
                  (min 2 initSize)
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | CedarType.intType =>
              match c_1 with
              | Prod.mk (CedarExpr.binaryApp (BinaryOp.sub) E1 E2) (PathSet.somepaths (List.nil)) =>
                EnumeratorCombinators.enumerating Enum.enum
                  (fun x1 =>
                    DecOpt.andOptList
                      [aux_dec initSize size' a_1 b_1 (Prod.mk E1 x1) (CedarType.intType),
                        EnumeratorCombinators.enumerating Enum.enum
                          (fun x2 => aux_dec initSize size' a_1 b_1 (Prod.mk E2 x2) (CedarType.intType))
                          (min 2 initSize)])
                  (min 2 initSize)
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | CedarType.intType =>
              match c_1 with
              | Prod.mk (CedarExpr.binaryApp (BinaryOp.mul) E1 E2) (PathSet.somepaths (List.nil)) =>
                EnumeratorCombinators.enumerating Enum.enum
                  (fun x1 =>
                    DecOpt.andOptList
                      [aux_dec initSize size' a_1 b_1 (Prod.mk E1 x1) (CedarType.intType),
                        EnumeratorCombinators.enumerating Enum.enum
                          (fun x2 => aux_dec initSize size' a_1 b_1 (Prod.mk E2 x2) (CedarType.intType))
                          (min 2 initSize)])
                  (min 2 initSize)
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | CedarType.recordTypeCons u_4 b T TR =>
              match c_1 with
              | Prod.mk (CedarExpr.recExprCons i e R) (PathSet.somepaths (List.nil)) =>
                DecOpt.andOptList
                  [DecOpt.decOpt (BEq.beq u_4 i) initSize,
                    DecOpt.andOptList
                      [DecOpt.decOpt (RecordType TR) initSize,
                        DecOpt.andOptList
                          [DecOpt.decOpt (RecordType TR) initSize,
                            EnumeratorCombinators.enumerating Enum.enum
                              (fun x =>
                                DecOpt.andOptList
                                  [aux_dec initSize size' a_1 b_1 (Prod.mk e x) T,
                                    EnumeratorCombinators.enumerating Enum.enum
                                      (fun rx => aux_dec initSize size' a_1 b_1 (Prod.mk R rx) TR) (min 2 initSize)])
                              (min 2 initSize)]]]
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | CedarType.setType T =>
              match c_1 with
              | Prod.mk (CedarExpr.setExprCons e (CedarExpr.setExprNil)) (PathSet.somepaths (List.nil)) =>
                EnumeratorCombinators.enumerating Enum.enum (fun x => aux_dec initSize size' a_1 b_1 (Prod.mk e x) T)
                  (min 2 initSize)
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | CedarType.setType T =>
              match c_1 with
              | Prod.mk (CedarExpr.setExprCons e R) (PathSet.somepaths (List.nil)) =>
                EnumeratorCombinators.enumerating Enum.enum
                  (fun x =>
                    DecOpt.andOptList
                      [aux_dec initSize size' a_1 b_1 (Prod.mk e x) T,
                        EnumeratorCombinators.enumerating Enum.enum
                          (fun rx => aux_dec initSize size' a_1 b_1 (Prod.mk R rx) (CedarType.setType T))
                          (min 2 initSize)])
                  (min 2 initSize)
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | CedarType.boolType (BoolType.tt) =>
              match c_1 with
              | Prod.mk (CedarExpr.unaryApp (UnaryOp.is n) e) (PathSet.somepaths (List.nil)) =>
                EnumeratorCombinators.enumeratingOpt
                  (EnumSizedSuchThat.enumSizedST (fun ns => WfCedarType ns (CedarType.entityType n)) initSize)
                  (fun ns =>
                    EnumeratorCombinators.enumeratingOpt
                      (EnumSizedSuchThat.enumSizedST (fun ets => DefinedEntities ets ns) initSize)
                      (fun ets =>
                        EnumeratorCombinators.enumerating Enum.enum
                          (fun acts =>
                            EnumeratorCombinators.enumerating Enum.enum
                              (fun R =>
                                DecOpt.andOptList
                                  [DecOpt.decOpt (Eq b_1 (Environment.MkEnvironment (Schema.MkSchema ets acts) R))
                                      initSize,
                                    EnumeratorCombinators.enumerating Enum.enum
                                      (fun x => aux_dec initSize size' a_1 b_1 (Prod.mk e x) (CedarType.entityType n))
                                      (min 2 initSize)])
                              (min 2 initSize))
                          (min 2 initSize))
                      (min 2 initSize))
                  (min 2 initSize)
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | CedarType.boolType (BoolType.ff) =>
              match c_1 with
              | Prod.mk (CedarExpr.unaryApp (UnaryOp.is N1) e) (PathSet.allpaths) =>
                EnumeratorCombinators.enumeratingOpt
                  (EnumSizedSuchThat.enumSizedST (fun ns => WfCedarType ns (CedarType.entityType N1)) initSize)
                  (fun ns =>
                    EnumeratorCombinators.enumeratingOpt
                      (EnumSizedSuchThat.enumSizedST (fun ets => DefinedEntities ets ns) initSize)
                      (fun ets =>
                        EnumeratorCombinators.enumerating Enum.enum
                          (fun N2 =>
                            DecOpt.andOptList
                              [DecOpt.decOpt (Ne N1 N2) initSize,
                                EnumeratorCombinators.enumerating Enum.enum
                                  (fun acts =>
                                    EnumeratorCombinators.enumerating Enum.enum
                                      (fun R =>
                                        DecOpt.andOptList
                                          [DecOpt.decOpt
                                              (Eq b_1 (Environment.MkEnvironment (Schema.MkSchema ets acts) R))
                                              initSize,
                                            EnumeratorCombinators.enumerating Enum.enum
                                              (fun x =>
                                                aux_dec initSize size' a_1 b_1 (Prod.mk e x) (CedarType.entityType N2))
                                              (min 2 initSize)])
                                      (min 2 initSize))
                                  (min 2 initSize)])
                          (min 2 initSize))
                      (min 2 initSize))
                  (min 2 initSize)
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match c_1 with
            | Prod.mk (CedarExpr.ite E1 E2 E3) (interExprs (mergeExprs x1 x2) x3) =>
              DecOpt.andOptList
                [aux_dec initSize size' a_1 b_1 (Prod.mk E1 x1) (CedarType.boolType (BoolType.anyBool)),
                  DecOpt.andOptList
                    [aux_dec initSize size' a_1 b_1 (Prod.mk E1 x1) (CedarType.boolType (BoolType.anyBool)),
                      EnumeratorCombinators.enumeratingOpt
                        (EnumSizedSuchThat.enumSizedST (fun T2 => SubType T2 t_1) initSize)
                        (fun T2 =>
                          DecOpt.andOptList
                            [aux_dec initSize size' (mergeExprs a_1 x1) b_1 (Prod.mk E2 x2) T2,
                              EnumeratorCombinators.enumeratingOpt
                                (EnumSizedSuchThat.enumSizedST (fun T3 => SubType T3 t_1) initSize)
                                (fun T3 => aux_dec initSize size' a_1 b_1 (Prod.mk E3 x3) T3) (min 2 initSize)])
                        (min 2 initSize)]]
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | CedarType.boolType (BoolType.ff) =>
              match c_1 with
              | Prod.mk (CedarExpr.binaryApp (BinaryOp.equals) E1 E2) (PathSet.allpaths) =>
                EnumeratorCombinators.enumerating Enum.enum
                  (fun ets =>
                    EnumeratorCombinators.enumeratingOpt
                      (EnumSizedSuchThat.enumSizedST (fun ns => DefinedEntities ets ns) initSize)
                      (fun ns =>
                        EnumeratorCombinators.enumerating Enum.enum
                          (fun N1 =>
                            DecOpt.andOptList
                              [DecOpt.decOpt (WfCedarType ns (CedarType.entityType N1)) initSize,
                                EnumeratorCombinators.enumerating Enum.enum
                                  (fun N2 =>
                                    DecOpt.andOptList
                                      [DecOpt.decOpt (Ne N1 N2) initSize,
                                        DecOpt.andOptList
                                          [DecOpt.decOpt (WfCedarType ns (CedarType.entityType N2)) initSize,
                                            EnumeratorCombinators.enumerating Enum.enum
                                              (fun acts =>
                                                EnumeratorCombinators.enumerating Enum.enum
                                                  (fun R =>
                                                    DecOpt.andOptList
                                                      [DecOpt.decOpt
                                                          (Eq b_1
                                                            (Environment.MkEnvironment (Schema.MkSchema ets acts) R))
                                                          initSize,
                                                        EnumeratorCombinators.enumerating Enum.enum
                                                          (fun x1 =>
                                                            DecOpt.andOptList
                                                              [aux_dec initSize size' a_1 b_1 (Prod.mk E1 x1)
                                                                  (CedarType.entityType N1),
                                                                EnumeratorCombinators.enumerating Enum.enum
                                                                  (fun x2 =>
                                                                    aux_dec initSize size' a_1 b_1 (Prod.mk E2 x2)
                                                                      (CedarType.entityType N2))
                                                                  (min 2 initSize)])
                                                          (min 2 initSize)])
                                                  (min 2 initSize))
                                              (min 2 initSize)]])
                                  (min 2 initSize)])
                          (min 2 initSize))
                      (min 2 initSize))
                  (min 2 initSize)
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | CedarType.boolType (BoolType.anyBool) =>
              match c_1 with
              | Prod.mk (CedarExpr.binaryApp (BinaryOp.equals) E1 E2) (PathSet.somepaths (List.nil)) =>
                EnumeratorCombinators.enumerating Enum.enum
                  (fun x1 =>
                    EnumeratorCombinators.enumeratingOpt
                      (EnumSizedSuchThat.enumSizedST (fun T1 => HasType a_1 b_1 (Prod.mk E1 x1) T1) initSize)
                      (fun T1 =>
                        EnumeratorCombinators.enumerating Enum.enum
                          (fun ets =>
                            EnumeratorCombinators.enumeratingOpt
                              (EnumSizedSuchThat.enumSizedST (fun ns => DefinedEntities ets ns) initSize)
                              (fun ns =>
                                EnumeratorCombinators.enumerating Enum.enum
                                  (fun T =>
                                    DecOpt.andOptList
                                      [DecOpt.decOpt (SubType T1 T) initSize,
                                        DecOpt.andOptList
                                          [DecOpt.decOpt (WfCedarType ns T) initSize,
                                            EnumeratorCombinators.enumerating Enum.enum
                                              (fun T2 =>
                                                DecOpt.andOptList
                                                  [DecOpt.decOpt (SubType T2 T) initSize,
                                                    EnumeratorCombinators.enumerating Enum.enum
                                                      (fun acts =>
                                                        EnumeratorCombinators.enumerating Enum.enum
                                                          (fun R =>
                                                            DecOpt.andOptList
                                                              [DecOpt.decOpt
                                                                  (Eq b_1
                                                                    (Environment.MkEnvironment
                                                                      (Schema.MkSchema ets acts) R))
                                                                  initSize,
                                                                EnumeratorCombinators.enumerating Enum.enum
                                                                  (fun x2 =>
                                                                    aux_dec initSize size' a_1 b_1 (Prod.mk E2 x2) T2)
                                                                  (min 2 initSize)])
                                                          (min 2 initSize))
                                                      (min 2 initSize)])
                                              (min 2 initSize)]])
                                  (min 2 initSize))
                              (min 2 initSize))
                          (min 2 initSize))
                      (min 2 initSize))
                  (min 2 initSize)
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | CedarType.boolType (BoolType.anyBool) =>
              match c_1 with
              | Prod.mk (CedarExpr.binaryApp (BinaryOp.mem) E1 E2) (PathSet.somepaths (List.nil)) =>
                EnumeratorCombinators.enumerating Enum.enum
                  (fun ets =>
                    EnumeratorCombinators.enumeratingOpt
                      (EnumSizedSuchThat.enumSizedST (fun ns => DefinedEntities ets ns) initSize)
                      (fun ns =>
                        EnumeratorCombinators.enumerating Enum.enum
                          (fun N1 =>
                            DecOpt.andOptList
                              [DecOpt.decOpt (WfCedarType ns (CedarType.entityType N1)) initSize,
                                EnumeratorCombinators.enumerating Enum.enum
                                  (fun N2 =>
                                    DecOpt.andOptList
                                      [DecOpt.decOpt (WfCedarType ns (CedarType.entityType N2)) initSize,
                                        EnumeratorCombinators.enumerating Enum.enum
                                          (fun acts =>
                                            EnumeratorCombinators.enumerating Enum.enum
                                              (fun R =>
                                                DecOpt.andOptList
                                                  [DecOpt.decOpt
                                                      (Eq b_1 (Environment.MkEnvironment (Schema.MkSchema ets acts) R))
                                                      initSize,
                                                    EnumeratorCombinators.enumerating Enum.enum
                                                      (fun x1 =>
                                                        DecOpt.andOptList
                                                          [aux_dec initSize size' a_1 b_1 (Prod.mk E1 x1)
                                                              (CedarType.entityType N1),
                                                            EnumeratorCombinators.enumerating Enum.enum
                                                              (fun x2 =>
                                                                aux_dec initSize size' a_1 b_1 (Prod.mk E2 x2)
                                                                  (CedarType.entityType N2))
                                                              (min 2 initSize)])
                                                      (min 2 initSize)])
                                              (min 2 initSize))
                                          (min 2 initSize)])
                                  (min 2 initSize)])
                          (min 2 initSize))
                      (min 2 initSize))
                  (min 2 initSize)
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | CedarType.boolType (BoolType.anyBool) =>
              match c_1 with
              | Prod.mk (CedarExpr.binaryApp (BinaryOp.mem) E1 E2) (PathSet.somepaths (List.nil)) =>
                EnumeratorCombinators.enumerating Enum.enum
                  (fun ets =>
                    EnumeratorCombinators.enumeratingOpt
                      (EnumSizedSuchThat.enumSizedST (fun ns => DefinedEntities ets ns) initSize)
                      (fun ns =>
                        EnumeratorCombinators.enumerating Enum.enum
                          (fun N1 =>
                            DecOpt.andOptList
                              [DecOpt.decOpt (WfCedarType ns (CedarType.entityType N1)) initSize,
                                EnumeratorCombinators.enumerating Enum.enum
                                  (fun N2 =>
                                    DecOpt.andOptList
                                      [DecOpt.decOpt (WfCedarType ns (CedarType.entityType N2)) initSize,
                                        EnumeratorCombinators.enumerating Enum.enum
                                          (fun acts =>
                                            EnumeratorCombinators.enumerating Enum.enum
                                              (fun R =>
                                                DecOpt.andOptList
                                                  [DecOpt.decOpt
                                                      (Eq b_1 (Environment.MkEnvironment (Schema.MkSchema ets acts) R))
                                                      initSize,
                                                    EnumeratorCombinators.enumerating Enum.enum
                                                      (fun x1 =>
                                                        DecOpt.andOptList
                                                          [aux_dec initSize size' a_1 b_1 (Prod.mk E1 x1)
                                                              (CedarType.entityType N1),
                                                            EnumeratorCombinators.enumerating Enum.enum
                                                              (fun x2 =>
                                                                aux_dec initSize size' a_1 b_1 (Prod.mk E2 x2)
                                                                  (CedarType.setType (CedarType.entityType N2)))
                                                              (min 2 initSize)])
                                                      (min 2 initSize)])
                                              (min 2 initSize))
                                          (min 2 initSize)])
                                  (min 2 initSize)])
                          (min 2 initSize))
                      (min 2 initSize))
                  (min 2 initSize)
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | CedarType.boolType (BoolType.anyBool) =>
              match c_1 with
              | Prod.mk (CedarExpr.binaryApp (BinaryOp.contains) E1 E2) (PathSet.somepaths (List.nil)) =>
                EnumeratorCombinators.enumerating Enum.enum
                  (fun x1 =>
                    EnumeratorCombinators.enumeratingOpt
                      (EnumSizedSuchThat.enumSizedST (fun T1 => HasType a_1 b_1 (Prod.mk E1 x1) T1) initSize)
                      (fun T1 =>
                        EnumeratorCombinators.enumerating Enum.enum
                          (fun ets =>
                            EnumeratorCombinators.enumeratingOpt
                              (EnumSizedSuchThat.enumSizedST (fun ns => DefinedEntities ets ns) initSize)
                              (fun ns =>
                                EnumeratorCombinators.enumerating Enum.enum
                                  (fun T =>
                                    DecOpt.andOptList
                                      [DecOpt.decOpt (SubType T1 T) initSize,
                                        DecOpt.andOptList
                                          [DecOpt.decOpt (WfCedarType ns T) initSize,
                                            EnumeratorCombinators.enumerating Enum.enum
                                              (fun T2 =>
                                                DecOpt.andOptList
                                                  [DecOpt.decOpt (SubType T2 T) initSize,
                                                    EnumeratorCombinators.enumerating Enum.enum
                                                      (fun acts =>
                                                        EnumeratorCombinators.enumerating Enum.enum
                                                          (fun R =>
                                                            DecOpt.andOptList
                                                              [DecOpt.decOpt
                                                                  (Eq b_1
                                                                    (Environment.MkEnvironment
                                                                      (Schema.MkSchema ets acts) R))
                                                                  initSize,
                                                                EnumeratorCombinators.enumerating Enum.enum
                                                                  (fun x2 =>
                                                                    aux_dec initSize size' a_1 b_1 (Prod.mk E2 x2)
                                                                      (CedarType.setType T2))
                                                                  (min 2 initSize)])
                                                          (min 2 initSize))
                                                      (min 2 initSize)])
                                              (min 2 initSize)]])
                                  (min 2 initSize))
                              (min 2 initSize))
                          (min 2 initSize))
                      (min 2 initSize))
                  (min 2 initSize)
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | CedarType.boolType (BoolType.anyBool) =>
              match c_1 with
              | Prod.mk (CedarExpr.binaryApp (BinaryOp.containsAll) E1 E2) (PathSet.somepaths (List.nil)) =>
                EnumeratorCombinators.enumerating Enum.enum
                  (fun ets =>
                    EnumeratorCombinators.enumeratingOpt
                      (EnumSizedSuchThat.enumSizedST (fun ns => DefinedEntities ets ns) initSize)
                      (fun ns =>
                        EnumeratorCombinators.enumerating Enum.enum
                          (fun T =>
                            DecOpt.andOptList
                              [DecOpt.decOpt (WfCedarType ns T) initSize,
                                EnumeratorCombinators.enumerating Enum.enum
                                  (fun T1 =>
                                    DecOpt.andOptList
                                      [DecOpt.decOpt (SubType T1 T) initSize,
                                        EnumeratorCombinators.enumerating Enum.enum
                                          (fun T2 =>
                                            DecOpt.andOptList
                                              [DecOpt.decOpt (SubType T2 T) initSize,
                                                EnumeratorCombinators.enumerating Enum.enum
                                                  (fun acts =>
                                                    EnumeratorCombinators.enumerating Enum.enum
                                                      (fun R =>
                                                        DecOpt.andOptList
                                                          [DecOpt.decOpt
                                                              (Eq b_1
                                                                (Environment.MkEnvironment (Schema.MkSchema ets acts)
                                                                  R))
                                                              initSize,
                                                            EnumeratorCombinators.enumerating Enum.enum
                                                              (fun x1 =>
                                                                DecOpt.andOptList
                                                                  [aux_dec initSize size' a_1 b_1 (Prod.mk E1 x1)
                                                                      (CedarType.setType T1),
                                                                    EnumeratorCombinators.enumerating Enum.enum
                                                                      (fun x2 =>
                                                                        aux_dec initSize size' a_1 b_1 (Prod.mk E2 x2)
                                                                          (CedarType.setType T2))
                                                                      (min 2 initSize)])
                                                              (min 2 initSize)])
                                                      (min 2 initSize))
                                                  (min 2 initSize)])
                                          (min 2 initSize)])
                                  (min 2 initSize)])
                          (min 2 initSize))
                      (min 2 initSize))
                  (min 2 initSize)
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | CedarType.boolType (BoolType.anyBool) =>
              match c_1 with
              | Prod.mk (CedarExpr.binaryApp (BinaryOp.containsAny) E1 E2) (PathSet.somepaths (List.nil)) =>
                EnumeratorCombinators.enumerating Enum.enum
                  (fun ets =>
                    EnumeratorCombinators.enumeratingOpt
                      (EnumSizedSuchThat.enumSizedST (fun ns => DefinedEntities ets ns) initSize)
                      (fun ns =>
                        EnumeratorCombinators.enumerating Enum.enum
                          (fun T =>
                            DecOpt.andOptList
                              [DecOpt.decOpt (WfCedarType ns T) initSize,
                                EnumeratorCombinators.enumerating Enum.enum
                                  (fun T1 =>
                                    DecOpt.andOptList
                                      [DecOpt.decOpt (SubType T1 T) initSize,
                                        EnumeratorCombinators.enumerating Enum.enum
                                          (fun T2 =>
                                            DecOpt.andOptList
                                              [DecOpt.decOpt (SubType T2 T) initSize,
                                                EnumeratorCombinators.enumerating Enum.enum
                                                  (fun acts =>
                                                    EnumeratorCombinators.enumerating Enum.enum
                                                      (fun R =>
                                                        DecOpt.andOptList
                                                          [DecOpt.decOpt
                                                              (Eq b_1
                                                                (Environment.MkEnvironment (Schema.MkSchema ets acts)
                                                                  R))
                                                              initSize,
                                                            EnumeratorCombinators.enumerating Enum.enum
                                                              (fun x1 =>
                                                                DecOpt.andOptList
                                                                  [aux_dec initSize size' a_1 b_1 (Prod.mk E1 x1)
                                                                      (CedarType.setType T1),
                                                                    EnumeratorCombinators.enumerating Enum.enum
                                                                      (fun x2 =>
                                                                        aux_dec initSize size' a_1 b_1 (Prod.mk E2 x2)
                                                                          (CedarType.setType T2))
                                                                      (min 2 initSize)])
                                                              (min 2 initSize)])
                                                      (min 2 initSize))
                                                  (min 2 initSize)])
                                          (min 2 initSize)])
                                  (min 2 initSize)])
                          (min 2 initSize))
                      (min 2 initSize))
                  (min 2 initSize)
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | CedarType.boolType (BoolType.anyBool) =>
              match c_1 with
              |
              Prod.mk (CedarExpr.hasAttr e F) (PathSet.somepaths (List.cons (CedarExpr.getAttr u_4 u_5) (List.nil))) =>
                DecOpt.andOptList
                  [DecOpt.decOpt (BEq.beq u_4 e) initSize,
                    DecOpt.andOptList
                      [DecOpt.decOpt (BEq.beq u_5 F) initSize,
                        EnumeratorCombinators.enumerating Enum.enum
                          (fun x =>
                            EnumeratorCombinators.enumeratingOpt
                              (EnumSizedSuchThat.enumSizedST (fun TE => HasType a_1 b_1 (Prod.mk e x) TE) initSize)
                              (fun TE =>
                                EnumeratorCombinators.enumerating Enum.enum
                                  (fun ets =>
                                    EnumeratorCombinators.enumeratingOpt
                                      (EnumSizedSuchThat.enumSizedST (fun ns => DefinedEntities ets ns) initSize)
                                      (fun ns =>
                                        EnumeratorCombinators.enumerating Enum.enum
                                          (fun acts =>
                                            EnumeratorCombinators.enumerating Enum.enum
                                              (fun R =>
                                                DecOpt.andOptList
                                                  [DecOpt.decOpt
                                                      (Eq b_1 (Environment.MkEnvironment (Schema.MkSchema ets acts) R))
                                                      initSize,
                                                    EnumeratorCombinators.enumerating Enum.enum
                                                      (fun T =>
                                                        DecOpt.decOpt
                                                          (BindAttrType ns (Prod.mk TE (Prod.mk F (Bool.true))) T)
                                                          initSize)
                                                      (min 2 initSize)])
                                              (min 2 initSize))
                                          (min 2 initSize))
                                      (min 2 initSize))
                                  (min 2 initSize))
                              (min 2 initSize))
                          (min 2 initSize)]]
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | CedarType.boolType (BoolType.tt) =>
              match c_1 with
              |
              Prod.mk (CedarExpr.hasAttr e F) (PathSet.somepaths (List.cons (CedarExpr.getAttr u_4 u_5) (List.nil))) =>
                DecOpt.andOptList
                  [DecOpt.decOpt (BEq.beq u_4 e) initSize,
                    DecOpt.andOptList
                      [DecOpt.decOpt (BEq.beq u_5 F) initSize,
                        EnumeratorCombinators.enumerating Enum.enum
                          (fun x =>
                            EnumeratorCombinators.enumeratingOpt
                              (EnumSizedSuchThat.enumSizedST (fun TE => HasType a_1 b_1 (Prod.mk e x) TE) initSize)
                              (fun TE =>
                                EnumeratorCombinators.enumerating Enum.enum
                                  (fun ets =>
                                    EnumeratorCombinators.enumeratingOpt
                                      (EnumSizedSuchThat.enumSizedST (fun ns => DefinedEntities ets ns) initSize)
                                      (fun ns =>
                                        EnumeratorCombinators.enumerating Enum.enum
                                          (fun acts =>
                                            EnumeratorCombinators.enumerating Enum.enum
                                              (fun R =>
                                                DecOpt.andOptList
                                                  [DecOpt.decOpt
                                                      (Eq b_1 (Environment.MkEnvironment (Schema.MkSchema ets acts) R))
                                                      initSize,
                                                    EnumeratorCombinators.enumerating Enum.enum
                                                      (fun T =>
                                                        DecOpt.decOpt
                                                          (BindAttrType ns (Prod.mk TE (Prod.mk F (Bool.false))) T)
                                                          initSize)
                                                      (min 2 initSize)])
                                              (min 2 initSize))
                                          (min 2 initSize))
                                      (min 2 initSize))
                                  (min 2 initSize))
                              (min 2 initSize))
                          (min 2 initSize)]]
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match c_1 with
            | Prod.mk (CedarExpr.getAttr e F) (PathSet.somepaths (List.nil)) =>
              DecOpt.andOptList
                [DecOpt.decOpt (Eq (validPathExpr (CedarExpr.getAttr e F) a_1) (Bool.true)) initSize,
                  EnumeratorCombinators.enumerating Enum.enum
                    (fun TE =>
                      DecOpt.andOptList
                        [DecOpt.decOpt (Eq (validPathExpr (CedarExpr.getAttr e F) a_1) (Bool.true)) initSize,
                          EnumeratorCombinators.enumeratingOpt
                            (EnumSizedSuchThat.enumSizedST
                              (fun ns => BindAttrType ns (Prod.mk TE (Prod.mk F (Bool.true))) t_1) initSize)
                            (fun ns =>
                              EnumeratorCombinators.enumeratingOpt
                                (EnumSizedSuchThat.enumSizedST (fun ets => DefinedEntities ets ns) initSize)
                                (fun ets =>
                                  EnumeratorCombinators.enumerating Enum.enum
                                    (fun acts =>
                                      EnumeratorCombinators.enumerating Enum.enum
                                        (fun R =>
                                          DecOpt.andOptList
                                            [DecOpt.decOpt
                                                (Eq b_1 (Environment.MkEnvironment (Schema.MkSchema ets acts) R))
                                                initSize,
                                              EnumeratorCombinators.enumerating Enum.enum
                                                (fun x => aux_dec initSize size' a_1 b_1 (Prod.mk e x) TE)
                                                (min 2 initSize)])
                                        (min 2 initSize))
                                    (min 2 initSize))
                                (min 2 initSize))
                            (min 2 initSize)])
                    (min 2 initSize)]
            | _ => Option.some Bool.false,
            fun _ =>
            match c_1 with
            | Prod.mk (CedarExpr.getAttr e F) (PathSet.somepaths (List.nil)) =>
              EnumeratorCombinators.enumerating Enum.enum
                (fun x =>
                  EnumeratorCombinators.enumeratingOpt
                    (EnumSizedSuchThat.enumSizedST (fun TE => HasType a_1 b_1 (Prod.mk e x) TE) initSize)
                    (fun TE =>
                      EnumeratorCombinators.enumeratingOpt
                        (EnumSizedSuchThat.enumSizedST
                          (fun ns => BindAttrType ns (Prod.mk TE (Prod.mk F (Bool.false))) t_1) initSize)
                        (fun ns =>
                          EnumeratorCombinators.enumeratingOpt
                            (EnumSizedSuchThat.enumSizedST (fun ets => DefinedEntities ets ns) initSize)
                            (fun ets =>
                              EnumeratorCombinators.enumerating Enum.enum
                                (fun acts =>
                                  EnumeratorCombinators.enumerating Enum.enum
                                    (fun R =>
                                      DecOpt.decOpt (Eq b_1 (Environment.MkEnvironment (Schema.MkSchema ets acts) R))
                                        initSize)
                                    (min 2 initSize))
                                (min 2 initSize))
                            (min 2 initSize))
                        (min 2 initSize))
                    (min 2 initSize))
                (min 2 initSize)
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | CedarType.boolType (BoolType.anyBool) =>
              match c_1 with
              |
              Prod.mk (CedarExpr.hasAttr e fn) (PathSet.somepaths (List.cons (CedarExpr.getAttr u_4 u_5) (List.nil))) =>
                DecOpt.andOptList
                  [DecOpt.decOpt (BEq.beq u_5 fn) initSize,
                    DecOpt.andOptList
                      [DecOpt.decOpt (BEq.beq u_4 e) initSize,
                        EnumeratorCombinators.enumerating Enum.enum
                          (fun ets =>
                            EnumeratorCombinators.enumerating Enum.enum
                              (fun n =>
                                EnumeratorCombinators.enumeratingOpt
                                  (EnumSizedSuchThat.enumSizedST
                                    (fun T => GetEntityAttr ets (Prod.mk n (Prod.mk fn (Bool.true))) T) initSize)
                                  (fun T =>
                                    EnumeratorCombinators.enumerating Enum.enum
                                      (fun acts =>
                                        EnumeratorCombinators.enumerating Enum.enum
                                          (fun R =>
                                            DecOpt.andOptList
                                              [DecOpt.decOpt
                                                  (Eq b_1 (Environment.MkEnvironment (Schema.MkSchema ets acts) R))
                                                  initSize,
                                                EnumeratorCombinators.enumerating Enum.enum
                                                  (fun x =>
                                                    aux_dec initSize size' a_1 b_1 (Prod.mk e x)
                                                      (CedarType.entityType n))
                                                  (min 2 initSize)])
                                          (min 2 initSize))
                                      (min 2 initSize))
                                  (min 2 initSize))
                              (min 2 initSize))
                          (min 2 initSize)]]
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match t_1 with
            | CedarType.boolType (BoolType.tt) =>
              match c_1 with
              |
              Prod.mk (CedarExpr.hasAttr e fn) (PathSet.somepaths (List.cons (CedarExpr.getAttr u_4 u_5) (List.nil))) =>
                DecOpt.andOptList
                  [DecOpt.decOpt (BEq.beq u_5 fn) initSize,
                    DecOpt.andOptList
                      [DecOpt.decOpt (BEq.beq u_4 e) initSize,
                        EnumeratorCombinators.enumerating Enum.enum
                          (fun ets =>
                            EnumeratorCombinators.enumerating Enum.enum
                              (fun n =>
                                EnumeratorCombinators.enumeratingOpt
                                  (EnumSizedSuchThat.enumSizedST
                                    (fun T => GetEntityAttr ets (Prod.mk n (Prod.mk fn (Bool.false))) T) initSize)
                                  (fun T =>
                                    EnumeratorCombinators.enumerating Enum.enum
                                      (fun acts =>
                                        EnumeratorCombinators.enumerating Enum.enum
                                          (fun R =>
                                            DecOpt.andOptList
                                              [DecOpt.decOpt
                                                  (Eq b_1 (Environment.MkEnvironment (Schema.MkSchema ets acts) R))
                                                  initSize,
                                                EnumeratorCombinators.enumerating Enum.enum
                                                  (fun x =>
                                                    aux_dec initSize size' a_1 b_1 (Prod.mk e x)
                                                      (CedarType.entityType n))
                                                  (min 2 initSize)])
                                          (min 2 initSize))
                                      (min 2 initSize))
                                  (min 2 initSize))
                              (min 2 initSize))
                          (min 2 initSize)]]
              | _ => Option.some Bool.false
            | _ => Option.some Bool.false,
            fun _ =>
            match c_1 with
            | Prod.mk (CedarExpr.getAttr e fn) (PathSet.somepaths (List.nil)) =>
              DecOpt.andOptList
                [DecOpt.decOpt (Eq (validPathExpr (CedarExpr.getAttr e fn) a_1) (Bool.true)) initSize,
                  EnumeratorCombinators.enumerating Enum.enum
                    (fun n =>
                      DecOpt.andOptList
                        [DecOpt.decOpt (Eq (validPathExpr (CedarExpr.getAttr e fn) a_1) (Bool.true)) initSize,
                          EnumeratorCombinators.enumeratingOpt
                            (EnumSizedSuchThat.enumSizedST
                              (fun ets => GetEntityAttr ets (Prod.mk n (Prod.mk fn (Bool.true))) t_1) initSize)
                            (fun ets =>
                              EnumeratorCombinators.enumerating Enum.enum
                                (fun acts =>
                                  EnumeratorCombinators.enumerating Enum.enum
                                    (fun R =>
                                      DecOpt.andOptList
                                        [DecOpt.decOpt (Eq b_1 (Environment.MkEnvironment (Schema.MkSchema ets acts) R))
                                            initSize,
                                          EnumeratorCombinators.enumerating Enum.enum
                                            (fun x =>
                                              aux_dec initSize size' a_1 b_1 (Prod.mk e x) (CedarType.entityType n))
                                            (min 2 initSize)])
                                    (min 2 initSize))
                                (min 2 initSize))
                            (min 2 initSize)])
                    (min 2 initSize)]
            | _ => Option.some Bool.false,
            fun _ =>
            match c_1 with
            | Prod.mk (CedarExpr.getAttr e fn) (PathSet.somepaths (List.nil)) =>
              EnumeratorCombinators.enumerating Enum.enum
                (fun n =>
                  EnumeratorCombinators.enumeratingOpt
                    (EnumSizedSuchThat.enumSizedST
                      (fun ets => GetEntityAttr ets (Prod.mk n (Prod.mk fn (Bool.false))) t_1) initSize)
                    (fun ets =>
                      EnumeratorCombinators.enumerating Enum.enum
                        (fun acts =>
                          EnumeratorCombinators.enumerating Enum.enum
                            (fun R =>
                              DecOpt.andOptList
                                [DecOpt.decOpt (Eq b_1 (Environment.MkEnvironment (Schema.MkSchema ets acts) R))
                                    initSize,
                                  EnumeratorCombinators.enumerating Enum.enum
                                    (fun x => aux_dec initSize size' a_1 b_1 (Prod.mk e x) (CedarType.entityType n))
                                    (min 2 initSize)])
                            (min 2 initSize))
                        (min 2 initSize))
                    (min 2 initSize))
                (min 2 initSize)
            | _ => Option.some Bool.false])
    fun size => aux_dec size size a_1 b_1 c_1 t_1

#derive_enumerator (fun (TE : CedarType) => HasType a_1_1 v_1_1 ex TE)




instance : ArbitrarySizedSuchThat (CedarExpr × PathSet) (fun ex_1 => HasType a_1 v_1 ex_1 t_1) where
  arbitrarySizedST :=
    let rec aux_arb (initSize : Nat) (size : Nat) (a_1 : PathSet) (v_1 : Environment) (t_1 : CedarType) :
      OptionT Plausible.Gen (CedarExpr × PathSet) :=
      (match size with
      | Nat.zero =>
        OptionTGen.backtrack
          [(1,
              match t_1 with
              | CedarType.boolType (BoolType.ff) => do
                let P ←
                  ArbitrarySizedSuchThat.arbitrarySizedST
                      (fun P => HasTypePrim v_1 P (CedarType.boolType (BoolType.ff))) initSize;
                return Prod.mk (CedarExpr.lit P) (PathSet.allpaths)
              | _ => OptionT.fail),
            (1,
              match DecOpt.decOpt (Ne t_1 (CedarType.boolType (BoolType.ff))) initSize with
              | Option.some Bool.true =>
                match DecOpt.decOpt (Ne t_1 (CedarType.boolType (BoolType.ff))) initSize with
                | Option.some Bool.true => do
                  let P ← ArbitrarySizedSuchThat.arbitrarySizedST (fun P => HasTypePrim v_1 P t_1) initSize;
                  return Prod.mk (CedarExpr.lit P) (PathSet.somepaths (List.nil))
                | _ => OptionT.fail
              | _ => OptionT.fail),
            (1, do
              let X ← ArbitrarySizedSuchThat.arbitrarySizedST (fun X => HasTypeVar v_1 X t_1) initSize;
              return Prod.mk (CedarExpr.var X) (PathSet.somepaths (List.nil))),
            (1,
              match t_1 with
              | CedarType.boolType (BoolType.tt) => do
                let P ← Plausible.Arbitrary.arbitrary;
                return
                    Prod.mk (CedarExpr.binaryApp (BinaryOp.equals) (CedarExpr.lit P) (CedarExpr.lit P))
                      (PathSet.somepaths (List.nil))
              | _ => OptionT.fail),
            (1,
              match t_1 with
              | CedarType.boolType (BoolType.ff) => do
                let (P1, P2) ← ArbitrarySizedSuchThat.arbitrarySizedST (fun (P1, P2) => Ne P1 P2) initSize;
                return
                    Prod.mk (CedarExpr.binaryApp (BinaryOp.equals) (CedarExpr.lit P1) (CedarExpr.lit P2))
                      (PathSet.allpaths)
              | _ => OptionT.fail),
            (1,
              match t_1 with
              | CedarType.recordTypeNil => return Prod.mk (CedarExpr.recExprNil) (PathSet.somepaths (List.nil))
              | _ => OptionT.fail)]
      | Nat.succ size' =>
        OptionTGen.backtrack
          [(1,
              match t_1 with
              | CedarType.boolType (BoolType.ff) => do
                let P ←
                  ArbitrarySizedSuchThat.arbitrarySizedST
                      (fun P => HasTypePrim v_1 P (CedarType.boolType (BoolType.ff))) initSize;
                return Prod.mk (CedarExpr.lit P) (PathSet.allpaths)
              | _ => OptionT.fail),
            (1,
              match DecOpt.decOpt (Ne t_1 (CedarType.boolType (BoolType.ff))) initSize with
              | Option.some Bool.true =>
                match DecOpt.decOpt (Ne t_1 (CedarType.boolType (BoolType.ff))) initSize with
                | Option.some Bool.true => do
                  let P ← ArbitrarySizedSuchThat.arbitrarySizedST (fun P => HasTypePrim v_1 P t_1) initSize;
                  return Prod.mk (CedarExpr.lit P) (PathSet.somepaths (List.nil))
                | _ => OptionT.fail
              | _ => OptionT.fail),
            (1, do
              let X ← ArbitrarySizedSuchThat.arbitrarySizedST (fun X => HasTypeVar v_1 X t_1) initSize;
              return Prod.mk (CedarExpr.var X) (PathSet.somepaths (List.nil))),
            (1,
              match t_1 with
              | CedarType.boolType (BoolType.tt) => do
                let P ← Plausible.Arbitrary.arbitrary;
                return
                    Prod.mk (CedarExpr.binaryApp (BinaryOp.equals) (CedarExpr.lit P) (CedarExpr.lit P))
                      (PathSet.somepaths (List.nil))
              | _ => OptionT.fail),
            (1,
              match t_1 with
              | CedarType.boolType (BoolType.ff) => do
                let (P1, P2) ← ArbitrarySizedSuchThat.arbitrarySizedST (fun (P1, P2) => Ne P1 P2) initSize;
                return
                    Prod.mk (CedarExpr.binaryApp (BinaryOp.equals) (CedarExpr.lit P1) (CedarExpr.lit P2))
                      (PathSet.allpaths)
              | _ => OptionT.fail),
            (1,
              match t_1 with
              | CedarType.recordTypeNil => return Prod.mk (CedarExpr.recExprNil) (PathSet.somepaths (List.nil))
              | _ => OptionT.fail),
            (Nat.succ size', do
              let vE1_x1 ← aux_arb initSize size' a_1 v_1 (CedarType.boolType (BoolType.tt));
              match vE1_x1 with
                | Prod.mk E1 x1 => do
                  let vE2_x2 ← aux_arb initSize size' (mergeExprs a_1 x1) v_1 t_1;
                  match vE2_x2 with
                    | Prod.mk E2 x2 => do
                      let E3 ← Plausible.Arbitrary.arbitrary;
                      return Prod.mk (CedarExpr.ite E1 E2 E3) (mergeExprs x1 x2)
                    | _ => OptionT.fail
                | _ => OptionT.fail),
            (Nat.succ size', do
              let vE3_x3 ← aux_arb initSize size' a_1 v_1 t_1;
              match vE3_x3 with
                | Prod.mk E3 x3 => do
                  let vE1_x1 ← aux_arb initSize size' a_1 v_1 (CedarType.boolType (BoolType.ff));
                  match vE1_x1 with
                    | Prod.mk E1 x1 => do
                      let E2 ← Plausible.Arbitrary.arbitrary;
                      return Prod.mk (CedarExpr.ite E1 E2 E3) x3
                    | _ => OptionT.fail
                | _ => OptionT.fail),
            (Nat.succ size', do
              let vE1_E2_x ← aux_arb initSize size' a_1 v_1 t_1;
              match vE1_E2_x with
                | Prod.mk (CedarExpr.ite E1 E2 (CedarExpr.lit (Prim.boolean (Bool.false)))) x =>
                  return Prod.mk (CedarExpr.andExpr E1 E2) x
                | _ => OptionT.fail),
            (Nat.succ size', do
              let vE1_E2_x ← aux_arb initSize size' a_1 v_1 t_1;
              match vE1_E2_x with
                | Prod.mk (CedarExpr.ite E1 (CedarExpr.lit (Prim.boolean (Bool.true))) E2) x =>
                  return Prod.mk (CedarExpr.orExpr E1 E2) x
                | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.boolType (BoolType.anyBool) => do
                let ve_x ← aux_arb initSize size' a_1 v_1 (CedarType.boolType (BoolType.anyBool));
                match ve_x with
                  | Prod.mk e x => return Prod.mk (CedarExpr.unaryApp (UnaryOp.not) e) (PathSet.somepaths (List.nil))
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.boolType (BoolType.ff) => do
                let ve_x ← aux_arb initSize size' a_1 v_1 (CedarType.boolType (BoolType.tt));
                match ve_x with
                  | Prod.mk e x => return Prod.mk (CedarExpr.unaryApp (UnaryOp.not) e) (PathSet.allpaths)
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.boolType (BoolType.tt) => do
                let ve_x ← aux_arb initSize size' a_1 v_1 (CedarType.boolType (BoolType.ff));
                match ve_x with
                  | Prod.mk e x => return Prod.mk (CedarExpr.unaryApp (UnaryOp.not) e) (PathSet.somepaths (List.nil))
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.intType => do
                let ve_x ← aux_arb initSize size' a_1 v_1 (CedarType.intType);
                match ve_x with
                  | Prod.mk e x => return Prod.mk (CedarExpr.unaryApp (UnaryOp.neg) e) (PathSet.somepaths (List.nil))
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.boolType (BoolType.anyBool) => do
                let ve_x ← aux_arb initSize size' a_1 v_1 (CedarType.stringType);
                match ve_x with
                  | Prod.mk e x => do
                    let P ← Plausible.Arbitrary.arbitrary;
                    return Prod.mk (CedarExpr.unaryApp (UnaryOp.like P) e) (PathSet.somepaths (List.nil))
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.boolType (BoolType.anyBool) => do
                let vE1_x1 ← aux_arb initSize size' a_1 v_1 (CedarType.intType);
                match vE1_x1 with
                  | Prod.mk E1 x1 => do
                    let vE2_x2 ← aux_arb initSize size' a_1 v_1 (CedarType.intType);
                    match vE2_x2 with
                      | Prod.mk E2 x2 =>
                        return Prod.mk (CedarExpr.binaryApp (BinaryOp.less) E1 E2) (PathSet.somepaths (List.nil))
                      | _ => OptionT.fail
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.boolType (BoolType.anyBool) => do
                let vE1_x1 ← aux_arb initSize size' a_1 v_1 (CedarType.intType);
                match vE1_x1 with
                  | Prod.mk E1 x1 => do
                    let vE2_x2 ← aux_arb initSize size' a_1 v_1 (CedarType.intType);
                    match vE2_x2 with
                      | Prod.mk E2 x2 =>
                        return Prod.mk (CedarExpr.binaryApp (BinaryOp.lessEq) E1 E2) (PathSet.somepaths (List.nil))
                      | _ => OptionT.fail
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.intType => do
                let vE1_x1 ← aux_arb initSize size' a_1 v_1 (CedarType.intType);
                match vE1_x1 with
                  | Prod.mk E1 x1 => do
                    let vE2_x2 ← aux_arb initSize size' a_1 v_1 (CedarType.intType);
                    match vE2_x2 with
                      | Prod.mk E2 x2 =>
                        return Prod.mk (CedarExpr.binaryApp (BinaryOp.add) E1 E2) (PathSet.somepaths (List.nil))
                      | _ => OptionT.fail
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.intType => do
                let vE1_x1 ← aux_arb initSize size' a_1 v_1 (CedarType.intType);
                match vE1_x1 with
                  | Prod.mk E1 x1 => do
                    let vE2_x2 ← aux_arb initSize size' a_1 v_1 (CedarType.intType);
                    match vE2_x2 with
                      | Prod.mk E2 x2 =>
                        return Prod.mk (CedarExpr.binaryApp (BinaryOp.sub) E1 E2) (PathSet.somepaths (List.nil))
                      | _ => OptionT.fail
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.intType => do
                let vE1_x1 ← aux_arb initSize size' a_1 v_1 (CedarType.intType);
                match vE1_x1 with
                  | Prod.mk E1 x1 => do
                    let vE2_x2 ← aux_arb initSize size' a_1 v_1 (CedarType.intType);
                    match vE2_x2 with
                      | Prod.mk E2 x2 =>
                        return Prod.mk (CedarExpr.binaryApp (BinaryOp.mul) E1 E2) (PathSet.somepaths (List.nil))
                      | _ => OptionT.fail
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.recordTypeCons i b T TR =>
                match DecOpt.decOpt (RecordType TR) initSize with
                | Option.some Bool.true =>
                  match DecOpt.decOpt (RecordType TR) initSize with
                  | Option.some Bool.true => do
                    let ve_x ← aux_arb initSize size' a_1 v_1 T;
                    match ve_x with
                      | Prod.mk e x => do
                        let vR_rx ← aux_arb initSize size' a_1 v_1 TR;
                        match vR_rx with
                          | Prod.mk R rx => return Prod.mk (CedarExpr.recExprCons i e R) (PathSet.somepaths (List.nil))
                          | _ => OptionT.fail
                      | _ => OptionT.fail
                  | _ => OptionT.fail
                | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.setType T => do
                let ve_x ← aux_arb initSize size' a_1 v_1 T;
                match ve_x with
                  | Prod.mk e x =>
                    return Prod.mk (CedarExpr.setExprCons e (CedarExpr.setExprNil)) (PathSet.somepaths (List.nil))
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.setType T => do
                let ve_x ← aux_arb initSize size' a_1 v_1 T;
                match ve_x with
                  | Prod.mk e x => do
                    let vR_rx ← aux_arb initSize size' a_1 v_1 (CedarType.setType T);
                    match vR_rx with
                      | Prod.mk R rx => return Prod.mk (CedarExpr.setExprCons e R) (PathSet.somepaths (List.nil))
                      | _ => OptionT.fail
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.boolType (BoolType.tt) => do
                let vets_acts_R ←
                  ArbitrarySizedSuchThat.arbitrarySizedST (fun vets_acts_R => Eq v_1 vets_acts_R) initSize;
                match vets_acts_R with
                  | Environment.MkEnvironment (Schema.MkSchema ets acts) R => do
                    let ns ← ArbitrarySizedSuchThat.arbitrarySizedST (fun ns => DefinedEntities ets ns) initSize;
                    do
                      let n ← Plausible.Arbitrary.arbitrary;
                      match DecOpt.decOpt (WfCedarType ns (CedarType.entityType n)) initSize with
                        | Option.some Bool.true => do
                          let e ← Plausible.Arbitrary.arbitrary;
                          do
                            let x ← Plausible.Arbitrary.arbitrary;
                            match DecOpt.decOpt (HasType a_1 v_1 (Prod.mk e x) (CedarType.entityType n)) initSize with
                              | Option.some Bool.true =>
                                return Prod.mk (CedarExpr.unaryApp (UnaryOp.is n) e) (PathSet.somepaths (List.nil))
                              | _ => OptionT.fail
                        | _ => OptionT.fail
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.boolType (BoolType.ff) => do
                let vets_acts_R ←
                  ArbitrarySizedSuchThat.arbitrarySizedST (fun vets_acts_R => Eq v_1 vets_acts_R) initSize;
                match vets_acts_R with
                  | Environment.MkEnvironment (Schema.MkSchema ets acts) R => do
                    let ns ← ArbitrarySizedSuchThat.arbitrarySizedST (fun ns => DefinedEntities ets ns) initSize;
                    do
                      let N1 ← Plausible.Arbitrary.arbitrary;
                      match DecOpt.decOpt (WfCedarType ns (CedarType.entityType N1)) initSize with
                        | Option.some Bool.true => do
                          let N2 ← Plausible.Arbitrary.arbitrary;
                          match DecOpt.decOpt (Ne N1 N2) initSize with
                            | Option.some Bool.true => do
                              let e ← Plausible.Arbitrary.arbitrary;
                              do
                                let x ← Plausible.Arbitrary.arbitrary;
                                match
                                    DecOpt.decOpt (HasType a_1 v_1 (Prod.mk e x) (CedarType.entityType N2))
                                      initSize with
                                  | Option.some Bool.true =>
                                    return Prod.mk (CedarExpr.unaryApp (UnaryOp.is N1) e) (PathSet.allpaths)
                                  | _ => OptionT.fail
                            | _ => OptionT.fail
                        | _ => OptionT.fail
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size', do
              let (vE3_x3, T3) ←
                ArbitrarySizedSuchThat.arbitrarySizedST (fun (vE3_x3, T3) => HasType a_1 v_1 vE3_x3 T3) initSize;
              match vE3_x3 with
                | Prod.mk E3 x3 =>
                  match DecOpt.decOpt (SubType T3 t_1) initSize with
                  | Option.some Bool.true => do
                    let T2 ← ArbitrarySizedSuchThat.arbitrarySizedST (fun T2 => SubType T2 t_1) initSize;
                    do
                      let E1 ← Plausible.Arbitrary.arbitrary;
                      do
                        let x1 ← Plausible.Arbitrary.arbitrary;
                        match
                            DecOpt.decOpt (HasType a_1 v_1 (Prod.mk E1 x1) (CedarType.boolType (BoolType.anyBool)))
                              initSize with
                          | Option.some Bool.true => do
                            let E2 ← Plausible.Arbitrary.arbitrary;
                            do
                              let x2 ← Plausible.Arbitrary.arbitrary;
                              match DecOpt.decOpt (HasType (mergeExprs a_1 x1) v_1 (Prod.mk E2 x2) T2) initSize with
                                | Option.some Bool.true =>
                                  return Prod.mk (CedarExpr.ite E1 E2 E3) (interExprs (mergeExprs x1 x2) x3)
                                | _ => OptionT.fail
                          | _ => OptionT.fail
                  | _ => OptionT.fail
                | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.boolType (BoolType.ff) => do
                let vets_acts_R ←
                  ArbitrarySizedSuchThat.arbitrarySizedST (fun vets_acts_R => Eq v_1 vets_acts_R) initSize;
                match vets_acts_R with
                  | Environment.MkEnvironment (Schema.MkSchema ets acts) R => do
                    let ns ← ArbitrarySizedSuchThat.arbitrarySizedST (fun ns => DefinedEntities ets ns) initSize;
                    do
                      let N1 ← Plausible.Arbitrary.arbitrary;
                      match DecOpt.decOpt (WfCedarType ns (CedarType.entityType N1)) initSize with
                        | Option.some Bool.true => do
                          let N2 ← Plausible.Arbitrary.arbitrary;
                          match DecOpt.decOpt (Ne N1 N2) initSize with
                            | Option.some Bool.true =>
                              match DecOpt.decOpt (WfCedarType ns (CedarType.entityType N2)) initSize with
                              | Option.some Bool.true => do
                                let E1 ← Plausible.Arbitrary.arbitrary;
                                do
                                  let x1 ← Plausible.Arbitrary.arbitrary;
                                  match
                                      DecOpt.decOpt (HasType a_1 v_1 (Prod.mk E1 x1) (CedarType.entityType N1))
                                        initSize with
                                    | Option.some Bool.true => do
                                      let E2 ← Plausible.Arbitrary.arbitrary;
                                      do
                                        let x2 ← Plausible.Arbitrary.arbitrary;
                                        match
                                            DecOpt.decOpt (HasType a_1 v_1 (Prod.mk E2 x2) (CedarType.entityType N2))
                                              initSize with
                                          | Option.some Bool.true =>
                                            return
                                              Prod.mk (CedarExpr.binaryApp (BinaryOp.equals) E1 E2) (PathSet.allpaths)
                                          | _ => OptionT.fail
                                    | _ => OptionT.fail
                              | _ => OptionT.fail
                            | _ => OptionT.fail
                        | _ => OptionT.fail
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.boolType (BoolType.anyBool) => do
                let vets_acts_R ←
                  ArbitrarySizedSuchThat.arbitrarySizedST (fun vets_acts_R => Eq v_1 vets_acts_R) initSize;
                match vets_acts_R with
                  | Environment.MkEnvironment (Schema.MkSchema ets acts) R => do
                    let ns ← ArbitrarySizedSuchThat.arbitrarySizedST (fun ns => DefinedEntities ets ns) initSize;
                    do
                      let T ← Plausible.Arbitrary.arbitrary;
                      match DecOpt.decOpt (WfCedarType ns T) initSize with
                        | Option.some Bool.true => do
                          let T1 ← Plausible.Arbitrary.arbitrary;
                          match DecOpt.decOpt (SubType T1 T) initSize with
                            | Option.some Bool.true => do
                              let T2 ← Plausible.Arbitrary.arbitrary;
                              match DecOpt.decOpt (SubType T2 T) initSize with
                                | Option.some Bool.true => do
                                  let E1 ← Plausible.Arbitrary.arbitrary;
                                  do
                                    let x1 ← Plausible.Arbitrary.arbitrary;
                                    match DecOpt.decOpt (HasType a_1 v_1 (Prod.mk E1 x1) T1) initSize with
                                      | Option.some Bool.true => do
                                        let E2 ← Plausible.Arbitrary.arbitrary;
                                        do
                                          let x2 ← Plausible.Arbitrary.arbitrary;
                                          match DecOpt.decOpt (HasType a_1 v_1 (Prod.mk E2 x2) T2) initSize with
                                            | Option.some Bool.true =>
                                              return
                                                Prod.mk (CedarExpr.binaryApp (BinaryOp.equals) E1 E2)
                                                  (PathSet.somepaths (List.nil))
                                            | _ => OptionT.fail
                                      | _ => OptionT.fail
                                | _ => OptionT.fail
                            | _ => OptionT.fail
                        | _ => OptionT.fail
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.boolType (BoolType.anyBool) => do
                let vets_acts_R ←
                  ArbitrarySizedSuchThat.arbitrarySizedST (fun vets_acts_R => Eq v_1 vets_acts_R) initSize;
                match vets_acts_R with
                  | Environment.MkEnvironment (Schema.MkSchema ets acts) R => do
                    let ns ← ArbitrarySizedSuchThat.arbitrarySizedST (fun ns => DefinedEntities ets ns) initSize;
                    do
                      let N1 ← Plausible.Arbitrary.arbitrary;
                      match DecOpt.decOpt (WfCedarType ns (CedarType.entityType N1)) initSize with
                        | Option.some Bool.true => do
                          let N2 ← Plausible.Arbitrary.arbitrary;
                          match DecOpt.decOpt (WfCedarType ns (CedarType.entityType N2)) initSize with
                            | Option.some Bool.true => do
                              let E1 ← Plausible.Arbitrary.arbitrary;
                              do
                                let x1 ← Plausible.Arbitrary.arbitrary;
                                match
                                    DecOpt.decOpt (HasType a_1 v_1 (Prod.mk E1 x1) (CedarType.entityType N1))
                                      initSize with
                                  | Option.some Bool.true => do
                                    let E2 ← Plausible.Arbitrary.arbitrary;
                                    do
                                      let x2 ← Plausible.Arbitrary.arbitrary;
                                      match
                                          DecOpt.decOpt (HasType a_1 v_1 (Prod.mk E2 x2) (CedarType.entityType N2))
                                            initSize with
                                        | Option.some Bool.true =>
                                          return
                                            Prod.mk (CedarExpr.binaryApp (BinaryOp.mem) E1 E2)
                                              (PathSet.somepaths (List.nil))
                                        | _ => OptionT.fail
                                  | _ => OptionT.fail
                            | _ => OptionT.fail
                        | _ => OptionT.fail
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.boolType (BoolType.anyBool) => do
                let vets_acts_R ←
                  ArbitrarySizedSuchThat.arbitrarySizedST (fun vets_acts_R => Eq v_1 vets_acts_R) initSize;
                match vets_acts_R with
                  | Environment.MkEnvironment (Schema.MkSchema ets acts) R => do
                    let ns ← ArbitrarySizedSuchThat.arbitrarySizedST (fun ns => DefinedEntities ets ns) initSize;
                    do
                      let N1 ← Plausible.Arbitrary.arbitrary;
                      match DecOpt.decOpt (WfCedarType ns (CedarType.entityType N1)) initSize with
                        | Option.some Bool.true => do
                          let N2 ← Plausible.Arbitrary.arbitrary;
                          match DecOpt.decOpt (WfCedarType ns (CedarType.entityType N2)) initSize with
                            | Option.some Bool.true => do
                              let E1 ← Plausible.Arbitrary.arbitrary;
                              do
                                let x1 ← Plausible.Arbitrary.arbitrary;
                                match
                                    DecOpt.decOpt (HasType a_1 v_1 (Prod.mk E1 x1) (CedarType.entityType N1))
                                      initSize with
                                  | Option.some Bool.true => do
                                    let E2 ← Plausible.Arbitrary.arbitrary;
                                    do
                                      let x2 ← Plausible.Arbitrary.arbitrary;
                                      match
                                          DecOpt.decOpt
                                            (HasType a_1 v_1 (Prod.mk E2 x2)
                                              (CedarType.setType (CedarType.entityType N2)))
                                            initSize with
                                        | Option.some Bool.true =>
                                          return
                                            Prod.mk (CedarExpr.binaryApp (BinaryOp.mem) E1 E2)
                                              (PathSet.somepaths (List.nil))
                                        | _ => OptionT.fail
                                  | _ => OptionT.fail
                            | _ => OptionT.fail
                        | _ => OptionT.fail
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.boolType (BoolType.anyBool) => do
                let vets_acts_R ←
                  ArbitrarySizedSuchThat.arbitrarySizedST (fun vets_acts_R => Eq v_1 vets_acts_R) initSize;
                match vets_acts_R with
                  | Environment.MkEnvironment (Schema.MkSchema ets acts) R => do
                    let ns ← ArbitrarySizedSuchThat.arbitrarySizedST (fun ns => DefinedEntities ets ns) initSize;
                    do
                      let T ← Plausible.Arbitrary.arbitrary;
                      match DecOpt.decOpt (WfCedarType ns T) initSize with
                        | Option.some Bool.true => do
                          let T1 ← Plausible.Arbitrary.arbitrary;
                          match DecOpt.decOpt (SubType T1 T) initSize with
                            | Option.some Bool.true => do
                              let T2 ← Plausible.Arbitrary.arbitrary;
                              match DecOpt.decOpt (SubType T2 T) initSize with
                                | Option.some Bool.true => do
                                  let E1 ← Plausible.Arbitrary.arbitrary;
                                  do
                                    let x1 ← Plausible.Arbitrary.arbitrary;
                                    match DecOpt.decOpt (HasType a_1 v_1 (Prod.mk E1 x1) T1) initSize with
                                      | Option.some Bool.true => do
                                        let E2 ← Plausible.Arbitrary.arbitrary;
                                        do
                                          let x2 ← Plausible.Arbitrary.arbitrary;
                                          match
                                              DecOpt.decOpt (HasType a_1 v_1 (Prod.mk E2 x2) (CedarType.setType T2))
                                                initSize with
                                            | Option.some Bool.true =>
                                              return
                                                Prod.mk (CedarExpr.binaryApp (BinaryOp.contains) E1 E2)
                                                  (PathSet.somepaths (List.nil))
                                            | _ => OptionT.fail
                                      | _ => OptionT.fail
                                | _ => OptionT.fail
                            | _ => OptionT.fail
                        | _ => OptionT.fail
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.boolType (BoolType.anyBool) => do
                let vets_acts_R ←
                  ArbitrarySizedSuchThat.arbitrarySizedST (fun vets_acts_R => Eq v_1 vets_acts_R) initSize;
                match vets_acts_R with
                  | Environment.MkEnvironment (Schema.MkSchema ets acts) R => do
                    let ns ← ArbitrarySizedSuchThat.arbitrarySizedST (fun ns => DefinedEntities ets ns) initSize;
                    do
                      let T ← Plausible.Arbitrary.arbitrary;
                      match DecOpt.decOpt (WfCedarType ns T) initSize with
                        | Option.some Bool.true => do
                          let T1 ← Plausible.Arbitrary.arbitrary;
                          match DecOpt.decOpt (SubType T1 T) initSize with
                            | Option.some Bool.true => do
                              let T2 ← Plausible.Arbitrary.arbitrary;
                              match DecOpt.decOpt (SubType T2 T) initSize with
                                | Option.some Bool.true => do
                                  let E1 ← Plausible.Arbitrary.arbitrary;
                                  do
                                    let x1 ← Plausible.Arbitrary.arbitrary;
                                    match
                                        DecOpt.decOpt (HasType a_1 v_1 (Prod.mk E1 x1) (CedarType.setType T1))
                                          initSize with
                                      | Option.some Bool.true => do
                                        let E2 ← Plausible.Arbitrary.arbitrary;
                                        do
                                          let x2 ← Plausible.Arbitrary.arbitrary;
                                          match
                                              DecOpt.decOpt (HasType a_1 v_1 (Prod.mk E2 x2) (CedarType.setType T2))
                                                initSize with
                                            | Option.some Bool.true =>
                                              return
                                                Prod.mk (CedarExpr.binaryApp (BinaryOp.containsAll) E1 E2)
                                                  (PathSet.somepaths (List.nil))
                                            | _ => OptionT.fail
                                      | _ => OptionT.fail
                                | _ => OptionT.fail
                            | _ => OptionT.fail
                        | _ => OptionT.fail
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.boolType (BoolType.anyBool) => do
                let vets_acts_R ←
                  ArbitrarySizedSuchThat.arbitrarySizedST (fun vets_acts_R => Eq v_1 vets_acts_R) initSize;
                match vets_acts_R with
                  | Environment.MkEnvironment (Schema.MkSchema ets acts) R => do
                    let ns ← ArbitrarySizedSuchThat.arbitrarySizedST (fun ns => DefinedEntities ets ns) initSize;
                    do
                      let T ← Plausible.Arbitrary.arbitrary;
                      match DecOpt.decOpt (WfCedarType ns T) initSize with
                        | Option.some Bool.true => do
                          let T1 ← Plausible.Arbitrary.arbitrary;
                          match DecOpt.decOpt (SubType T1 T) initSize with
                            | Option.some Bool.true => do
                              let T2 ← Plausible.Arbitrary.arbitrary;
                              match DecOpt.decOpt (SubType T2 T) initSize with
                                | Option.some Bool.true => do
                                  let E1 ← Plausible.Arbitrary.arbitrary;
                                  do
                                    let x1 ← Plausible.Arbitrary.arbitrary;
                                    match
                                        DecOpt.decOpt (HasType a_1 v_1 (Prod.mk E1 x1) (CedarType.setType T1))
                                          initSize with
                                      | Option.some Bool.true => do
                                        let E2 ← Plausible.Arbitrary.arbitrary;
                                        do
                                          let x2 ← Plausible.Arbitrary.arbitrary;
                                          match
                                              DecOpt.decOpt (HasType a_1 v_1 (Prod.mk E2 x2) (CedarType.setType T2))
                                                initSize with
                                            | Option.some Bool.true =>
                                              return
                                                Prod.mk (CedarExpr.binaryApp (BinaryOp.containsAny) E1 E2)
                                                  (PathSet.somepaths (List.nil))
                                            | _ => OptionT.fail
                                      | _ => OptionT.fail
                                | _ => OptionT.fail
                            | _ => OptionT.fail
                        | _ => OptionT.fail
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.boolType (BoolType.anyBool) => do
                let (ve_x, TE) ←
                  ArbitrarySizedSuchThat.arbitrarySizedST (fun (ve_x, TE) => HasType a_1 v_1 ve_x TE) initSize;
                match ve_x with
                  | Prod.mk e x => do
                    let vets_acts_R ←
                      ArbitrarySizedSuchThat.arbitrarySizedST (fun vets_acts_R => Eq v_1 vets_acts_R) initSize;
                    match vets_acts_R with
                      | Environment.MkEnvironment (Schema.MkSchema ets acts) R => do
                        let ns ← Plausible.Arbitrary.arbitrary;
                        match DecOpt.decOpt (DefinedEntities ets ns) initSize with
                          | Option.some Bool.true => do
                            let T ← Plausible.Arbitrary.arbitrary;
                            do
                              let F ← Plausible.Arbitrary.arbitrary;
                              match DecOpt.decOpt (BindAttrType ns (Prod.mk TE (Prod.mk F (Bool.true))) T) initSize with
                                | Option.some Bool.true =>
                                  return
                                    Prod.mk (CedarExpr.hasAttr e F)
                                      (PathSet.somepaths (List.cons (CedarExpr.getAttr e F) (List.nil)))
                                | _ => OptionT.fail
                          | _ => OptionT.fail
                      | _ => OptionT.fail
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.boolType (BoolType.tt) => do
                let (ve_x, TE) ←
                  ArbitrarySizedSuchThat.arbitrarySizedST (fun (ve_x, TE) => HasType a_1 v_1 ve_x TE) initSize;
                match ve_x with
                  | Prod.mk e x => do
                    let vets_acts_R ←
                      ArbitrarySizedSuchThat.arbitrarySizedST (fun vets_acts_R => Eq v_1 vets_acts_R) initSize;
                    match vets_acts_R with
                      | Environment.MkEnvironment (Schema.MkSchema ets acts) R => do
                        let ns ← Plausible.Arbitrary.arbitrary;
                        match DecOpt.decOpt (DefinedEntities ets ns) initSize with
                          | Option.some Bool.true => do
                            let T ← Plausible.Arbitrary.arbitrary;
                            do
                              let F ← Plausible.Arbitrary.arbitrary;
                              match
                                  DecOpt.decOpt (BindAttrType ns (Prod.mk TE (Prod.mk F (Bool.false))) T) initSize with
                                | Option.some Bool.true =>
                                  return
                                    Prod.mk (CedarExpr.hasAttr e F)
                                      (PathSet.somepaths (List.cons (CedarExpr.getAttr e F) (List.nil)))
                                | _ => OptionT.fail
                          | _ => OptionT.fail
                      | _ => OptionT.fail
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size', do
              let vets_acts_R ←
                ArbitrarySizedSuchThat.arbitrarySizedST (fun vets_acts_R => Eq v_1 vets_acts_R) initSize;
              match vets_acts_R with
                | Environment.MkEnvironment (Schema.MkSchema ets acts) R => do
                  let ns ← ArbitrarySizedSuchThat.arbitrarySizedST (fun ns => DefinedEntities ets ns) initSize;
                  do
                    let e ← Plausible.Arbitrary.arbitrary;
                    do
                      let F ← Plausible.Arbitrary.arbitrary;
                      match DecOpt.decOpt (Eq (validPathExpr (CedarExpr.getAttr e F) a_1) (Bool.true)) initSize with
                        | Option.some Bool.true => do
                          let TE ← Plausible.Arbitrary.arbitrary;
                          match DecOpt.decOpt (BindAttrType ns (Prod.mk TE (Prod.mk F (Bool.true))) t_1) initSize with
                            | Option.some Bool.true => do
                              let x ← Plausible.Arbitrary.arbitrary;
                              match DecOpt.decOpt (HasType a_1 v_1 (Prod.mk e x) TE) initSize with
                                | Option.some Bool.true =>
                                  return Prod.mk (CedarExpr.getAttr e F) (PathSet.somepaths (List.nil))
                                | _ => OptionT.fail
                            | _ => OptionT.fail
                        | _ => OptionT.fail
                | _ => OptionT.fail),
            (Nat.succ size', do
              let (ns, vTE_F) ←
                ArbitrarySizedSuchThat.arbitrarySizedST (fun (ns, vTE_F) => BindAttrType ns vTE_F t_1) initSize;
              match vTE_F with
                | Prod.mk TE (Prod.mk F (Bool.false)) => do
                  let vets_acts_R ←
                    ArbitrarySizedSuchThat.arbitrarySizedST (fun vets_acts_R => Eq v_1 vets_acts_R) initSize;
                  match vets_acts_R with
                    | Environment.MkEnvironment (Schema.MkSchema ets acts) R =>
                      match DecOpt.decOpt (DefinedEntities ets ns) initSize with
                      | Option.some Bool.true => do
                        let e ← Plausible.Arbitrary.arbitrary;
                        do
                          let x ← Plausible.Arbitrary.arbitrary;
                          match DecOpt.decOpt (HasType a_1 v_1 (Prod.mk e x) TE) initSize with
                            | Option.some Bool.true =>
                              return Prod.mk (CedarExpr.getAttr e F) (PathSet.somepaths (List.nil))
                            | _ => OptionT.fail
                      | _ => OptionT.fail
                    | _ => OptionT.fail
                | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.boolType (BoolType.anyBool) => do
                let vets_acts_R ←
                  ArbitrarySizedSuchThat.arbitrarySizedST (fun vets_acts_R => Eq v_1 vets_acts_R) initSize;
                match vets_acts_R with
                  | Environment.MkEnvironment (Schema.MkSchema ets acts) R => do
                    let (vn_fn, T) ←
                      ArbitrarySizedSuchThat.arbitrarySizedST (fun (vn_fn, T) => GetEntityAttr ets vn_fn T) initSize;
                    match vn_fn with
                      | Prod.mk n (Prod.mk fn (Bool.true)) => do
                        let ve_x ← aux_arb initSize size' a_1 v_1 (CedarType.entityType n);
                        match ve_x with
                          | Prod.mk e x =>
                            return
                              Prod.mk (CedarExpr.hasAttr e fn)
                                (PathSet.somepaths (List.cons (CedarExpr.getAttr e fn) (List.nil)))
                          | _ => OptionT.fail
                      | _ => OptionT.fail
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size',
              match t_1 with
              | CedarType.boolType (BoolType.tt) => do
                let vets_acts_R ←
                  ArbitrarySizedSuchThat.arbitrarySizedST (fun vets_acts_R => Eq v_1 vets_acts_R) initSize;
                match vets_acts_R with
                  | Environment.MkEnvironment (Schema.MkSchema ets acts) R => do
                    let (vn_fn, T) ←
                      ArbitrarySizedSuchThat.arbitrarySizedST (fun (vn_fn, T) => GetEntityAttr ets vn_fn T) initSize;
                    match vn_fn with
                      | Prod.mk n (Prod.mk fn (Bool.false)) => do
                        let ve_x ← aux_arb initSize size' a_1 v_1 (CedarType.entityType n);
                        match ve_x with
                          | Prod.mk e x =>
                            return
                              Prod.mk (CedarExpr.hasAttr e fn)
                                (PathSet.somepaths (List.cons (CedarExpr.getAttr e fn) (List.nil)))
                          | _ => OptionT.fail
                      | _ => OptionT.fail
                  | _ => OptionT.fail
              | _ => OptionT.fail),
            (Nat.succ size', do
              let vets_acts_R ←
                ArbitrarySizedSuchThat.arbitrarySizedST (fun vets_acts_R => Eq v_1 vets_acts_R) initSize;
              match vets_acts_R with
                | Environment.MkEnvironment (Schema.MkSchema ets acts) R => do
                  let vn_fn ←
                    ArbitrarySizedSuchThat.arbitrarySizedST (fun vn_fn => GetEntityAttr ets vn_fn t_1) initSize;
                  match vn_fn with
                    | Prod.mk n (Prod.mk fn (Bool.true)) => do
                      let e ← Plausible.Arbitrary.arbitrary;
                      match DecOpt.decOpt (Eq (validPathExpr (CedarExpr.getAttr e fn) a_1) (Bool.true)) initSize with
                        | Option.some Bool.true => do
                          let x ← Plausible.Arbitrary.arbitrary;
                          match DecOpt.decOpt (HasType a_1 v_1 (Prod.mk e x) (CedarType.entityType n)) initSize with
                            | Option.some Bool.true =>
                              return Prod.mk (CedarExpr.getAttr e fn) (PathSet.somepaths (List.nil))
                            | _ => OptionT.fail
                        | _ => OptionT.fail
                    | _ => OptionT.fail
                | _ => OptionT.fail),
            (Nat.succ size', do
              let vets_acts_R ←
                ArbitrarySizedSuchThat.arbitrarySizedST (fun vets_acts_R => Eq v_1 vets_acts_R) initSize;
              match vets_acts_R with
                | Environment.MkEnvironment (Schema.MkSchema ets acts) R => do
                  let vn_fn ←
                    ArbitrarySizedSuchThat.arbitrarySizedST (fun vn_fn => GetEntityAttr ets vn_fn t_1) initSize;
                  match vn_fn with
                    | Prod.mk n (Prod.mk fn (Bool.false)) => do
                      let ve_x ← aux_arb initSize size' a_1 v_1 (CedarType.entityType n);
                      match ve_x with
                        | Prod.mk e x => return Prod.mk (CedarExpr.getAttr e fn) (PathSet.somepaths (List.nil))
                        | _ => OptionT.fail
                    | _ => OptionT.fail
                | _ => OptionT.fail)])
    fun size => aux_arb size size a_1 v_1 t_1

#derive_generator (fun (ex : (CedarExpr × PathSet)) => HasType a v ex t)
