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

#derive_enumerator (fun (ns_1 : _)=> DefinedName ns_1 n)

#derive_enumerator (fun (ns : _) => WfCedarType ns t)

#derive_enumerator (fun (ets : _) => DefinedEntities ets ns)

#derive_enumerator (fun (ns_1 : _) => WfRecordType ns_1 r)

#derive_enumerator (fun (ns : _) => BindAttrType ns a t_1)

#derive_enumerator (fun (E : _) => LookupEntityAttr E (fn, b) t_1_1)

#derive_enumerator (fun (ets : _) => GetEntityAttr ets a t_1)

#derive_enumerator (fun (R2 : _) => RecordType R2)

#derive_enumerator (fun (TE_1 : _) => SubType T2 TE_1)
#derive_enumerator (fun (T2 : _) => SubType T2 TE_1)

#check DecOpt.decOpt

mutual
  def aux_dec (initSize : Nat) (size : Nat) (a_1 : PathSet) (v_1 : Environment) (e_1 : CedarExpr × PathSet)
      (t_1 : CedarType) : Option Bool :=
      (match size with
      | Nat.zero =>
        match (e_1, t_1) with
        | (Prod.mk (CedarExpr.lit P) (PathSet.allpaths), CedarType.boolType (BoolType.ff)) =>
          DecOpt.andOptList
            [DecOpt.decOpt (HasTypePrim v_1 P (CedarType.boolType (BoolType.ff))) initSize,
              DecOpt.decOpt (HasTypePrim v_1 P (CedarType.boolType (BoolType.ff))) initSize]
        | (Prod.mk (CedarExpr.lit P) (PathSet.somepaths (List.nil)), _) =>
          DecOpt.andOptList
            [DecOpt.decOpt (HasTypePrim v_1 P t_1) initSize,
              DecOpt.andOptList
                [DecOpt.decOpt (Ne t_1 (CedarType.boolType (BoolType.ff))) initSize,
                  DecOpt.andOptList
                    [DecOpt.decOpt (HasTypePrim v_1 P t_1) initSize,
                      DecOpt.decOpt (Ne t_1 (CedarType.boolType (BoolType.ff))) initSize]]]
        | (Prod.mk (CedarExpr.var X) (PathSet.somepaths (List.nil)), _) =>
          DecOpt.andOptList
            [DecOpt.decOpt (HasTypeVar v_1 X t_1) initSize, DecOpt.decOpt (HasTypeVar v_1 X t_1) initSize]
        | (Prod.mk (CedarExpr.binaryApp (BinaryOp.equals) (CedarExpr.lit P) (CedarExpr.lit u_4)) (PathSet.somepaths (List.nil)), CedarType.boolType (BoolType.tt)) =>
          DecOpt.decOpt (BEq.beq u_4 P) initSize
        | (Prod.mk (CedarExpr.binaryApp (BinaryOp.equals) (CedarExpr.lit P1) (CedarExpr.lit P2)) (PathSet.allpaths), CedarType.boolType (BoolType.ff)) =>
          DecOpt.andOptList [DecOpt.decOpt (Ne P1 P2) initSize, DecOpt.decOpt (Ne P1 P2) initSize]
        | (Prod.mk (CedarExpr.recExprNil) (PathSet.somepaths (List.nil)), CedarType.recordTypeNil) =>
          Option.some Bool.true
        | _ => Option.some Bool.false
      | Nat.succ size' =>
        match (e_1, t_1) with
        -- Base cases (same as zero case)
        | (Prod.mk (CedarExpr.lit P) (PathSet.allpaths), CedarType.boolType (BoolType.ff)) =>
          DecOpt.andOptList
            [DecOpt.decOpt (HasTypePrim v_1 P (CedarType.boolType (BoolType.ff))) initSize,
              DecOpt.decOpt (HasTypePrim v_1 P (CedarType.boolType (BoolType.ff))) initSize]
        | (Prod.mk (CedarExpr.lit P) (PathSet.somepaths (List.nil)), _) =>
          DecOpt.andOptList
            [DecOpt.decOpt (HasTypePrim v_1 P t_1) initSize,
              DecOpt.andOptList
                [DecOpt.decOpt (Ne t_1 (CedarType.boolType (BoolType.ff))) initSize,
                  DecOpt.andOptList
                    [DecOpt.decOpt (HasTypePrim v_1 P t_1) initSize,
                      DecOpt.decOpt (Ne t_1 (CedarType.boolType (BoolType.ff))) initSize]]]
        | (Prod.mk (CedarExpr.var X) (PathSet.somepaths (List.nil)), _) =>
          DecOpt.andOptList
            [DecOpt.decOpt (HasTypeVar v_1 X t_1) initSize, DecOpt.decOpt (HasTypeVar v_1 X t_1) initSize]
        | (Prod.mk (CedarExpr.binaryApp (BinaryOp.equals) (CedarExpr.lit P) (CedarExpr.lit u_4)) (PathSet.somepaths (List.nil)), CedarType.boolType (BoolType.tt)) =>
          DecOpt.decOpt (BEq.beq u_4 P) initSize
        | (Prod.mk (CedarExpr.binaryApp (BinaryOp.equals) (CedarExpr.lit P1) (CedarExpr.lit P2)) (PathSet.allpaths), CedarType.boolType (BoolType.ff)) =>
          DecOpt.andOptList [DecOpt.decOpt (Ne P1 P2) initSize, DecOpt.decOpt (Ne P1 P2) initSize]
        | (Prod.mk (CedarExpr.recExprNil) (PathSet.somepaths (List.nil)), CedarType.recordTypeNil) =>
          Option.some Bool.true
        -- Recursive cases (only in successor case)
        | (Prod.mk (CedarExpr.ite E1 E2 E3) u, _) =>
          DecOpt.checkerBacktrack
            [fun (_ : Unit) =>
              EnumeratorCombinators.enumerating Enum.enum
                (fun x1 =>
                  EnumeratorCombinators.enumerating Enum.enum
                    (fun x2 =>
                      DecOpt.andOptList
                        [aux_dec initSize size' a_1 v_1 (Prod.mk E1 x1) (CedarType.boolType (BoolType.tt)),
                          DecOpt.andOptList
                            [aux_dec initSize size' (mergeExprs a_1 x1) v_1 (Prod.mk E2 x2) t_1,
                              DecOpt.decOpt (Eq u (mergeExprs x1 x2)) initSize]])
                    (initSize))
                (initSize),
              fun (_ : Unit) =>
              DecOpt.andOptList
                [aux_dec initSize size' a_1 v_1 (Prod.mk E3 u) t_1,
                  EnumeratorCombinators.enumerating Enum.enum
                    (fun x1 =>
                      DecOpt.andOptList
                        [aux_dec initSize size' a_1 v_1 (Prod.mk E3 u) t_1,
                          aux_dec initSize size' a_1 v_1 (Prod.mk E1 x1) (CedarType.boolType (BoolType.ff))])
                    (initSize)]]
        | (Prod.mk (CedarExpr.andExpr E1 E2) x, _) =>
          DecOpt.andOptList
            [aux_dec initSize size' a_1 v_1
                (Prod.mk (CedarExpr.ite E1 E2 (CedarExpr.lit (Prim.boolean (Bool.false)))) x) t_1,
              aux_dec initSize size' a_1 v_1
                (Prod.mk (CedarExpr.ite E1 E2 (CedarExpr.lit (Prim.boolean (Bool.false)))) x) t_1]
        | (Prod.mk (CedarExpr.orExpr E1 E2) x, _) =>
          DecOpt.andOptList
            [aux_dec initSize size' a_1 v_1
                (Prod.mk (CedarExpr.ite E1 (CedarExpr.lit (Prim.boolean (Bool.true))) E2) x) t_1,
              aux_dec initSize size' a_1 v_1
                (Prod.mk (CedarExpr.ite E1 (CedarExpr.lit (Prim.boolean (Bool.true))) E2) x) t_1]
        | (Prod.mk (CedarExpr.unaryApp (UnaryOp.not) e) (PathSet.somepaths (List.nil)), CedarType.boolType (BoolType.anyBool)) =>
          EnumeratorCombinators.enumerating Enum.enum
            (fun x => aux_dec initSize size' a_1 v_1 (Prod.mk e x) (CedarType.boolType (BoolType.anyBool)))
            (initSize)
        | (Prod.mk (CedarExpr.unaryApp (UnaryOp.not) e) (PathSet.allpaths), CedarType.boolType (BoolType.ff)) =>
          EnumeratorCombinators.enumerating Enum.enum
            (fun x => aux_dec initSize size' a_1 v_1 (Prod.mk e x) (CedarType.boolType (BoolType.tt)))
            (initSize)
        | (Prod.mk (CedarExpr.unaryApp (UnaryOp.not) e) (PathSet.somepaths (List.nil)), CedarType.boolType (BoolType.tt)) =>
          EnumeratorCombinators.enumerating Enum.enum
            (fun x => aux_dec initSize size' a_1 v_1 (Prod.mk e x) (CedarType.boolType (BoolType.ff)))
            (initSize)
        | (Prod.mk (CedarExpr.unaryApp (UnaryOp.neg) e) (PathSet.somepaths (List.nil)), CedarType.intType) =>
          EnumeratorCombinators.enumerating Enum.enum
            (fun x => aux_dec initSize size' a_1 v_1 (Prod.mk e x) (CedarType.intType)) (initSize)
        | (Prod.mk (CedarExpr.unaryApp (UnaryOp.like P) e) (PathSet.somepaths (List.nil)), CedarType.boolType (BoolType.anyBool)) =>
          EnumeratorCombinators.enumerating Enum.enum
            (fun x => aux_dec initSize size' a_1 v_1 (Prod.mk e x) (CedarType.stringType)) (initSize)
        | (Prod.mk (CedarExpr.binaryApp (BinaryOp.less) E1 E2) (PathSet.somepaths (List.nil)), CedarType.boolType (BoolType.anyBool)) =>
          EnumeratorCombinators.enumerating Enum.enum
            (fun x1 =>
              DecOpt.andOptList
                [aux_dec initSize size' a_1 v_1 (Prod.mk E1 x1) (CedarType.intType),
                  EnumeratorCombinators.enumerating Enum.enum
                    (fun x2 => aux_dec initSize size' a_1 v_1 (Prod.mk E2 x2) (CedarType.intType))
                    (initSize)])
            (initSize)
        | (Prod.mk (CedarExpr.binaryApp (BinaryOp.lessEq) E1 E2) (PathSet.somepaths (List.nil)), CedarType.boolType (BoolType.anyBool)) =>
          EnumeratorCombinators.enumerating Enum.enum
            (fun x1 =>
              DecOpt.andOptList
                [aux_dec initSize size' a_1 v_1 (Prod.mk E1 x1) (CedarType.intType),
                  EnumeratorCombinators.enumerating Enum.enum
                    (fun x2 => aux_dec initSize size' a_1 v_1 (Prod.mk E2 x2) (CedarType.intType))
                    (initSize)])
            (initSize)
        | (Prod.mk (CedarExpr.binaryApp (BinaryOp.add) E1 E2) (PathSet.somepaths (List.nil)), CedarType.intType) =>
          EnumeratorCombinators.enumerating Enum.enum
            (fun x1 =>
              DecOpt.andOptList
                [aux_dec initSize size' a_1 v_1 (Prod.mk E1 x1) (CedarType.intType),
                  EnumeratorCombinators.enumerating Enum.enum
                    (fun x2 => aux_dec initSize size' a_1 v_1 (Prod.mk E2 x2) (CedarType.intType))
                    (initSize)])
            (initSize)
        | (Prod.mk (CedarExpr.binaryApp (BinaryOp.sub) E1 E2) (PathSet.somepaths (List.nil)), CedarType.intType) =>
          EnumeratorCombinators.enumerating Enum.enum
            (fun x1 =>
              DecOpt.andOptList
                [aux_dec initSize size' a_1 v_1 (Prod.mk E1 x1) (CedarType.intType),
                  EnumeratorCombinators.enumerating Enum.enum
                    (fun x2 => aux_dec initSize size' a_1 v_1 (Prod.mk E2 x2) (CedarType.intType))
                    (initSize)])
            (initSize)
        | (Prod.mk (CedarExpr.binaryApp (BinaryOp.mul) E1 E2) (PathSet.somepaths (List.nil)), CedarType.intType) =>
          EnumeratorCombinators.enumerating Enum.enum
            (fun x1 =>
              DecOpt.andOptList
                [aux_dec initSize size' a_1 v_1 (Prod.mk E1 x1) (CedarType.intType),
                  EnumeratorCombinators.enumerating Enum.enum
                    (fun x2 => aux_dec initSize size' a_1 v_1 (Prod.mk E2 x2) (CedarType.intType))
                    (initSize)])
            (initSize)
        | _ => Option.some Bool.false)
  def aux_enum (initSize : Nat) (size : Nat) (a_1_1_1 : PathSet) (v_1_1_1 : Environment)
      (ex_1 : CedarExpr × PathSet) : OptionT Enumerator CedarType :=
      (match size with
      | Nat.zero =>
        EnumeratorCombinators.enumerate
          [match ex_1 with
            | Prod.mk (CedarExpr.lit P) (PathSet.allpaths) =>
              match DecOpt.decOpt (HasTypePrim v_1_1_1 P (CedarType.boolType (BoolType.ff))) initSize with
              | Option.some Bool.true =>
                match DecOpt.decOpt (HasTypePrim v_1_1_1 P (CedarType.boolType (BoolType.ff))) initSize with
                | Option.some Bool.true => return CedarType.boolType (BoolType.ff)
                | _ => OptionT.fail
              | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.lit P) (PathSet.somepaths (List.nil)) => do
              let TE_1 ← EnumSizedSuchThat.enumSizedST (fun TE_1 => HasTypePrim v_1_1_1 P TE_1) initSize;
              match DecOpt.decOpt (Ne TE_1 (CedarType.boolType (BoolType.ff))) initSize with
                | Option.some Bool.true => return TE_1
                | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.var X) (PathSet.somepaths (List.nil)) => do
              let TE_1 ← EnumSizedSuchThat.enumSizedST (fun TE_1 => HasTypeVar v_1_1_1 X TE_1) initSize;
              return TE_1
            | _ => OptionT.fail,
            match ex_1 with
            |
            Prod.mk (CedarExpr.binaryApp (BinaryOp.equals) (CedarExpr.lit P) (CedarExpr.lit u_4))
                (PathSet.somepaths (List.nil)) =>
              match DecOpt.decOpt (BEq.beq u_4 P) initSize with
              | Option.some Bool.true => return CedarType.boolType (BoolType.tt)
              | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            |
            Prod.mk (CedarExpr.binaryApp (BinaryOp.equals) (CedarExpr.lit P1) (CedarExpr.lit P2)) (PathSet.allpaths) =>
              match DecOpt.decOpt (Ne P1 P2) initSize with
              | Option.some Bool.true =>
                match DecOpt.decOpt (Ne P1 P2) initSize with
                | Option.some Bool.true => return CedarType.boolType (BoolType.ff)
                | _ => OptionT.fail
              | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.recExprNil) (PathSet.somepaths (List.nil)) => return CedarType.recordTypeNil
            | _ => OptionT.fail]
      | Nat.succ size' =>
        EnumeratorCombinators.enumerate
          [match ex_1 with
            | Prod.mk (CedarExpr.lit P) (PathSet.allpaths) =>
              match DecOpt.decOpt (HasTypePrim v_1_1_1 P (CedarType.boolType (BoolType.ff))) initSize with
              | Option.some Bool.true =>
                match DecOpt.decOpt (HasTypePrim v_1_1_1 P (CedarType.boolType (BoolType.ff))) initSize with
                | Option.some Bool.true => return CedarType.boolType (BoolType.ff)
                | _ => OptionT.fail
              | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.lit P) (PathSet.somepaths (List.nil)) => do
              let TE_1 ← EnumSizedSuchThat.enumSizedST (fun TE_1 => HasTypePrim v_1_1_1 P TE_1) initSize;
              match DecOpt.decOpt (Ne TE_1 (CedarType.boolType (BoolType.ff))) initSize with
                | Option.some Bool.true => return TE_1
                | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.var X) (PathSet.somepaths (List.nil)) => do
              let TE_1 ← EnumSizedSuchThat.enumSizedST (fun TE_1 => HasTypeVar v_1_1_1 X TE_1) initSize;
              return TE_1
            | _ => OptionT.fail,
            match ex_1 with
            |
            Prod.mk (CedarExpr.binaryApp (BinaryOp.equals) (CedarExpr.lit P) (CedarExpr.lit u_4))
                (PathSet.somepaths (List.nil)) =>
              match DecOpt.decOpt (BEq.beq u_4 P) initSize with
              | Option.some Bool.true => return CedarType.boolType (BoolType.tt)
              | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            |
            Prod.mk (CedarExpr.binaryApp (BinaryOp.equals) (CedarExpr.lit P1) (CedarExpr.lit P2)) (PathSet.allpaths) =>
              match DecOpt.decOpt (Ne P1 P2) initSize with
              | Option.some Bool.true =>
                match DecOpt.decOpt (Ne P1 P2) initSize with
                | Option.some Bool.true => return CedarType.boolType (BoolType.ff)
                | _ => OptionT.fail
              | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.recExprNil) (PathSet.somepaths (List.nil)) => return CedarType.recordTypeNil
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.ite E1 E2 E3) u => do
              let x1 ← Enum.enum;
              do
                let x2 ← Enum.enum;
                match DecOpt.decOpt (Eq u (mergeExprs x1 x2)) initSize with
                  | Option.some Bool.true =>
                    match
                      (aux_dec initSize 0 a_1_1_1 v_1_1_1 (Prod.mk E1 x1) (CedarType.boolType (BoolType.tt)))
                     with
                    | Option.some Bool.true => do
                      let TE_1 ← aux_enum initSize size' (mergeExprs a_1_1_1 x1) v_1_1_1 (Prod.mk E2 x2);
                      return TE_1
                    | _ => OptionT.fail
                  | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.ite E1 E2 E3) x3 => do
              let TE_1 ← aux_enum initSize size' a_1_1_1 v_1_1_1 (Prod.mk E3 x3);
              do
                let x1 ← Enum.enum;
                match (aux_dec initSize 0 a_1_1_1 v_1_1_1 (Prod.mk E1 x1) (CedarType.boolType (BoolType.ff))) with
                  | Option.some Bool.true => return TE_1
                  | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.andExpr E1 E2) x => do
              let TE_1 ←
                aux_enum initSize size' a_1_1_1 v_1_1_1
                    (Prod.mk (CedarExpr.ite E1 E2 (CedarExpr.lit (Prim.boolean (Bool.false)))) x);
              return TE_1
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.orExpr E1 E2) x => do
              let TE_1 ←
                aux_enum initSize size' a_1_1_1 v_1_1_1
                    (Prod.mk (CedarExpr.ite E1 (CedarExpr.lit (Prim.boolean (Bool.true))) E2) x);
              return TE_1
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.unaryApp (UnaryOp.not) e) (PathSet.somepaths (List.nil)) => do
              let x ← Enum.enum;
              match aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk e x) (CedarType.boolType (BoolType.anyBool)) with
                | Option.some Bool.true => return CedarType.boolType (BoolType.anyBool)
                | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.unaryApp (UnaryOp.not) e) (PathSet.allpaths) => do
              let x ← Enum.enum;
              match
                  aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk e x) (CedarType.boolType (BoolType.tt)) with
                | Option.some Bool.true => return CedarType.boolType (BoolType.ff)
                | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.unaryApp (UnaryOp.not) e) (PathSet.somepaths (List.nil)) => do
              let x ← Enum.enum;
              match
                  aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk e x) (CedarType.boolType (BoolType.ff)) with
                | Option.some Bool.true => return CedarType.boolType (BoolType.tt)
                | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.unaryApp (UnaryOp.neg) e) (PathSet.somepaths (List.nil)) => do
              let x ← Enum.enum;
              match aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk e x) (CedarType.intType) with
                | Option.some Bool.true => return CedarType.intType
                | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.unaryApp (UnaryOp.like P) e) (PathSet.somepaths (List.nil)) => do
              let x ← Enum.enum;
              match aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk e x) (CedarType.stringType) with
                | Option.some Bool.true => return CedarType.boolType (BoolType.anyBool)
                | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.binaryApp (BinaryOp.less) E1 E2) (PathSet.somepaths (List.nil)) => do
              let x1 ← Enum.enum;
              match aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk E1 x1) (CedarType.intType) with
                | Option.some Bool.true => do
                  let x2 ← Enum.enum;
                  match aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk E2 x2) (CedarType.intType) with
                    | Option.some Bool.true => return CedarType.boolType (BoolType.anyBool)
                    | _ => OptionT.fail
                | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.binaryApp (BinaryOp.lessEq) E1 E2) (PathSet.somepaths (List.nil)) => do
              let x1 ← Enum.enum;
              match aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk E1 x1) (CedarType.intType) with
                | Option.some Bool.true => do
                  let x2 ← Enum.enum;
                  match aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk E2 x2) (CedarType.intType) with
                    | Option.some Bool.true => return CedarType.boolType (BoolType.anyBool)
                    | _ => OptionT.fail
                | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.binaryApp (BinaryOp.add) E1 E2) (PathSet.somepaths (List.nil)) => do
              let x1 ← Enum.enum;
              match aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk E1 x1) (CedarType.intType) with
                | Option.some Bool.true => do
                  let x2 ← Enum.enum;
                  match aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk E2 x2) (CedarType.intType) with
                    | Option.some Bool.true => return CedarType.intType
                    | _ => OptionT.fail
                | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.binaryApp (BinaryOp.sub) E1 E2) (PathSet.somepaths (List.nil)) => do
              let x1 ← Enum.enum;
              match aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk E1 x1) (CedarType.intType) with
                | Option.some Bool.true => do
                  let x2 ← Enum.enum;
                  match aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk E2 x2) (CedarType.intType) with
                    | Option.some Bool.true => return CedarType.intType
                    | _ => OptionT.fail
                | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.binaryApp (BinaryOp.mul) E1 E2) (PathSet.somepaths (List.nil)) => do
              let x1 ← Enum.enum;
              match aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk E1 x1) (CedarType.intType) with
                | Option.some Bool.true => do
                  let x2 ← Enum.enum;
                  match aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk E2 x2) (CedarType.intType) with
                    | Option.some Bool.true => return CedarType.intType
                    | _ => OptionT.fail
                | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.recExprCons i e R) (PathSet.somepaths (List.nil)) => do
              let rx ← Enum.enum;
              do
                let TR ← aux_enum initSize size' a_1_1_1 v_1_1_1 (Prod.mk R rx);
                match DecOpt.decOpt (RecordType TR) initSize with
                  | Option.some Bool.true => do
                    let x ← Enum.enum;
                    do
                      let T ← aux_enum initSize size' a_1_1_1 v_1_1_1 (Prod.mk e x);
                      do
                        let b ← Enum.enum;
                        return CedarType.recordTypeCons i b T TR
                  | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.setExprCons e (CedarExpr.setExprNil)) (PathSet.somepaths (List.nil)) => do
              let x ← Enum.enum;
              do
                let T ← aux_enum initSize size' a_1_1_1 v_1_1_1 (Prod.mk e x);
                return CedarType.setType T
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.setExprCons e R) (PathSet.somepaths (List.nil)) => do
              let x ← Enum.enum;
              do
                let T ← aux_enum initSize size' a_1_1_1 v_1_1_1 (Prod.mk e x);
                do
                  let rx ← Enum.enum;
                  match aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk R rx) (CedarType.setType T) with
                    | Option.some Bool.true => return CedarType.setType T
                    | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.unaryApp (UnaryOp.is n) e) (PathSet.somepaths (List.nil)) => do
              let ns ← EnumSizedSuchThat.enumSizedST (fun ns => WfCedarType ns (CedarType.entityType n)) initSize;
              do
                let ets ← EnumSizedSuchThat.enumSizedST (fun ets => DefinedEntities ets ns) initSize;
                do
                  let acts ← Enum.enum;
                  do
                    let R ← Enum.enum;
                    match
                        DecOpt.decOpt (Eq v_1_1_1 (Environment.MkEnvironment (Schema.MkSchema ets acts) R))
                          initSize with
                      | Option.some Bool.true => do
                        let x ← Enum.enum;
                        match
                            aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk e x) (CedarType.entityType n) with
                          | Option.some Bool.true => return CedarType.boolType (BoolType.tt)
                          | _ => OptionT.fail
                      | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.unaryApp (UnaryOp.is N1) e) (PathSet.allpaths) => do
              let ns ← EnumSizedSuchThat.enumSizedST (fun ns => WfCedarType ns (CedarType.entityType N1)) initSize;
              do
                let ets ← EnumSizedSuchThat.enumSizedST (fun ets => DefinedEntities ets ns) initSize;
                do
                  let N2 ← Enum.enum;
                  match DecOpt.decOpt (Ne N1 N2) initSize with
                    | Option.some Bool.true => do
                      let acts ← Enum.enum;
                      do
                        let R ← Enum.enum;
                        match
                            DecOpt.decOpt (Eq v_1_1_1 (Environment.MkEnvironment (Schema.MkSchema ets acts) R))
                              initSize with
                          | Option.some Bool.true => do
                            let x ← Enum.enum;
                            match
                                aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk e x) (CedarType.entityType N2) with
                              | Option.some Bool.true => return CedarType.boolType (BoolType.ff)
                              | _ => OptionT.fail
                          | _ => OptionT.fail
                    | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.ite E1 E2 E3) u => do
              let x1 ← Enum.enum;
              do
                let x2 ← Enum.enum;
                match
                    aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk E1 x1) (CedarType.boolType (BoolType.anyBool)) with
                  | Option.some Bool.true => do
                    let T2 ← aux_enum initSize size' (mergeExprs a_1_1_1 x1) v_1_1_1 (Prod.mk E2 x2);
                    do
                      let TE_1 ← EnumSizedSuchThat.enumSizedST (fun TE_1 => SubType T2 TE_1) initSize;
                      do
                        let T3 ← Enum.enum;
                        match DecOpt.decOpt (SubType T3 TE_1) initSize with
                          | Option.some Bool.true => do
                            let x3 ← Enum.enum;
                            match aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk E3 x3) T3 with
                              | Option.some Bool.true =>
                                match DecOpt.decOpt (Eq u (interExprs (mergeExprs x1 x2) x3)) initSize with
                                | Option.some Bool.true => return TE_1
                                | _ => OptionT.fail
                              | _ => OptionT.fail
                          | _ => OptionT.fail
                  | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.binaryApp (BinaryOp.equals) E1 E2) (PathSet.allpaths) => do
              let ets ← Enum.enum;
              do
                let ns ← EnumSizedSuchThat.enumSizedST (fun ns => DefinedEntities ets ns) initSize;
                do
                  let N1 ← Enum.enum;
                  match DecOpt.decOpt (WfCedarType ns (CedarType.entityType N1)) initSize with
                    | Option.some Bool.true => do
                      let N2 ← Enum.enum;
                      match DecOpt.decOpt (Ne N1 N2) initSize with
                        | Option.some Bool.true =>
                          match DecOpt.decOpt (WfCedarType ns (CedarType.entityType N2)) initSize with
                          | Option.some Bool.true => do
                            let acts ← Enum.enum;
                            do
                              let R ← Enum.enum;
                              match
                                  DecOpt.decOpt (Eq v_1_1_1 (Environment.MkEnvironment (Schema.MkSchema ets acts) R))
                                    initSize with
                                | Option.some Bool.true => do
                                  let x1 ← Enum.enum;
                                  match
                                      aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk E1 x1) (CedarType.entityType N1) with
                                    | Option.some Bool.true => do
                                      let x2 ← Enum.enum;
                                      match
                                          aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk E2 x2) (CedarType.entityType N2)
                                            with
                                        | Option.some Bool.true => return CedarType.boolType (BoolType.ff)
                                        | _ => OptionT.fail
                                    | _ => OptionT.fail
                                | _ => OptionT.fail
                          | _ => OptionT.fail
                        | _ => OptionT.fail
                    | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.binaryApp (BinaryOp.equals) E1 E2) (PathSet.somepaths (List.nil)) => do
              let x1 ← Enum.enum;
              do
                let T1 ← aux_enum initSize size' a_1_1_1 v_1_1_1 (Prod.mk E1 x1);
                do
                  let ets ← Enum.enum;
                  do
                    let ns ← EnumSizedSuchThat.enumSizedST (fun ns => DefinedEntities ets ns) initSize;
                    do
                      let T ← Enum.enum;
                      match DecOpt.decOpt (SubType T1 T) initSize with
                        | Option.some Bool.true =>
                          match DecOpt.decOpt (WfCedarType ns T) initSize with
                          | Option.some Bool.true => do
                            let T2 ← Enum.enum;
                            match DecOpt.decOpt (SubType T2 T) initSize with
                              | Option.some Bool.true => do
                                let acts ← Enum.enum;
                                do
                                  let R ← Enum.enum;
                                  match
                                      DecOpt.decOpt
                                        (Eq v_1_1_1 (Environment.MkEnvironment (Schema.MkSchema ets acts) R))
                                        initSize with
                                    | Option.some Bool.true => do
                                      let x2 ← Enum.enum;
                                      match aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk E2 x2) T2 with
                                        | Option.some Bool.true => return CedarType.boolType (BoolType.anyBool)
                                        | _ => OptionT.fail
                                    | _ => OptionT.fail
                              | _ => OptionT.fail
                          | _ => OptionT.fail
                        | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.binaryApp (BinaryOp.mem) E1 E2) (PathSet.somepaths (List.nil)) => do
              let ets ← Enum.enum;
              do
                let ns ← EnumSizedSuchThat.enumSizedST (fun ns => DefinedEntities ets ns) initSize;
                do
                  let N1 ← Enum.enum;
                  match DecOpt.decOpt (WfCedarType ns (CedarType.entityType N1)) initSize with
                    | Option.some Bool.true => do
                      let N2 ← Enum.enum;
                      match DecOpt.decOpt (WfCedarType ns (CedarType.entityType N2)) initSize with
                        | Option.some Bool.true => do
                          let acts ← Enum.enum;
                          do
                            let R ← Enum.enum;
                            match
                                DecOpt.decOpt (Eq v_1_1_1 (Environment.MkEnvironment (Schema.MkSchema ets acts) R))
                                  initSize with
                              | Option.some Bool.true => do
                                let x1 ← Enum.enum;
                                match
                                    aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk E1 x1) (CedarType.entityType N1) with
                                  | Option.some Bool.true => do
                                    let x2 ← Enum.enum;
                                    match
                                        aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk E2 x2) (CedarType.entityType N2) with
                                      | Option.some Bool.true => return CedarType.boolType (BoolType.anyBool)
                                      | _ => OptionT.fail
                                  | _ => OptionT.fail
                              | _ => OptionT.fail
                        | _ => OptionT.fail
                    | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.binaryApp (BinaryOp.mem) E1 E2) (PathSet.somepaths (List.nil)) => do
              let ets ← Enum.enum;
              do
                let ns ← EnumSizedSuchThat.enumSizedST (fun ns => DefinedEntities ets ns) initSize;
                do
                  let N1 ← Enum.enum;
                  match DecOpt.decOpt (WfCedarType ns (CedarType.entityType N1)) initSize with
                    | Option.some Bool.true => do
                      let N2 ← Enum.enum;
                      match DecOpt.decOpt (WfCedarType ns (CedarType.entityType N2)) initSize with
                        | Option.some Bool.true => do
                          let acts ← Enum.enum;
                          do
                            let R ← Enum.enum;
                            match
                                DecOpt.decOpt (Eq v_1_1_1 (Environment.MkEnvironment (Schema.MkSchema ets acts) R))
                                  initSize with
                              | Option.some Bool.true => do
                                let x1 ← Enum.enum;
                                match
                                    aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk E1 x1) (CedarType.entityType N1) with
                                  | Option.some Bool.true => do
                                    let x2 ← Enum.enum;
                                    match
                                        aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk E2 x2)
                                            (CedarType.setType (CedarType.entityType N2)) with
                                      | Option.some Bool.true => return CedarType.boolType (BoolType.anyBool)
                                      | _ => OptionT.fail
                                  | _ => OptionT.fail
                              | _ => OptionT.fail
                        | _ => OptionT.fail
                    | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.binaryApp (BinaryOp.contains) E1 E2) (PathSet.somepaths (List.nil)) => do
              let x1 ← Enum.enum;
              do
                let T1 ← aux_enum initSize size' a_1_1_1 v_1_1_1 (Prod.mk E1 x1);
                do
                  let ets ← Enum.enum;
                  do
                    let ns ← EnumSizedSuchThat.enumSizedST (fun ns => DefinedEntities ets ns) initSize;
                    do
                      let T ← Enum.enum;
                      match DecOpt.decOpt (SubType T1 T) initSize with
                        | Option.some Bool.true =>
                          match DecOpt.decOpt (WfCedarType ns T) initSize with
                          | Option.some Bool.true => do
                            let T2 ← Enum.enum;
                            match DecOpt.decOpt (SubType T2 T) initSize with
                              | Option.some Bool.true => do
                                let acts ← Enum.enum;
                                do
                                  let R ← Enum.enum;
                                  match
                                      DecOpt.decOpt
                                        (Eq v_1_1_1 (Environment.MkEnvironment (Schema.MkSchema ets acts) R))
                                        initSize with
                                    | Option.some Bool.true => do
                                      let x2 ← Enum.enum;
                                      match
                                          aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk E2 x2) (CedarType.setType T2) with
                                        | Option.some Bool.true => return CedarType.boolType (BoolType.anyBool)
                                        | _ => OptionT.fail
                                    | _ => OptionT.fail
                              | _ => OptionT.fail
                          | _ => OptionT.fail
                        | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.binaryApp (BinaryOp.containsAll) E1 E2) (PathSet.somepaths (List.nil)) => do
              let ets ← Enum.enum;
              do
                let ns ← EnumSizedSuchThat.enumSizedST (fun ns => DefinedEntities ets ns) initSize;
                do
                  let T ← Enum.enum;
                  match DecOpt.decOpt (WfCedarType ns T) initSize with
                    | Option.some Bool.true => do
                      let T1 ← Enum.enum;
                      match DecOpt.decOpt (SubType T1 T) initSize with
                        | Option.some Bool.true => do
                          let T2 ← Enum.enum;
                          match DecOpt.decOpt (SubType T2 T) initSize with
                            | Option.some Bool.true => do
                              let acts ← Enum.enum;
                              do
                                let R ← Enum.enum;
                                match
                                    DecOpt.decOpt (Eq v_1_1_1 (Environment.MkEnvironment (Schema.MkSchema ets acts) R))
                                      initSize with
                                  | Option.some Bool.true => do
                                    let x1 ← Enum.enum;
                                    match
                                        aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk E1 x1) (CedarType.setType T1) with
                                      | Option.some Bool.true => do
                                        let x2 ← Enum.enum;
                                        match
                                            aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk E2 x2) (CedarType.setType T2) with
                                          | Option.some Bool.true => return CedarType.boolType (BoolType.anyBool)
                                          | _ => OptionT.fail
                                      | _ => OptionT.fail
                                  | _ => OptionT.fail
                            | _ => OptionT.fail
                        | _ => OptionT.fail
                    | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.binaryApp (BinaryOp.containsAny) E1 E2) (PathSet.somepaths (List.nil)) => do
              let ets ← Enum.enum;
              do
                let ns ← EnumSizedSuchThat.enumSizedST (fun ns => DefinedEntities ets ns) initSize;
                do
                  let T ← Enum.enum;
                  match DecOpt.decOpt (WfCedarType ns T) initSize with
                    | Option.some Bool.true => do
                      let T1 ← Enum.enum;
                      match DecOpt.decOpt (SubType T1 T) initSize with
                        | Option.some Bool.true => do
                          let T2 ← Enum.enum;
                          match DecOpt.decOpt (SubType T2 T) initSize with
                            | Option.some Bool.true => do
                              let acts ← Enum.enum;
                              do
                                let R ← Enum.enum;
                                match
                                    DecOpt.decOpt (Eq v_1_1_1 (Environment.MkEnvironment (Schema.MkSchema ets acts) R))
                                      initSize with
                                  | Option.some Bool.true => do
                                    let x1 ← Enum.enum;
                                    match
                                        aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk E1 x1) (CedarType.setType T1) with
                                      | Option.some Bool.true => do
                                        let x2 ← Enum.enum;
                                        match
                                            aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk E2 x2) (CedarType.setType T2) with
                                          | Option.some Bool.true => return CedarType.boolType (BoolType.anyBool)
                                          | _ => OptionT.fail
                                      | _ => OptionT.fail
                                  | _ => OptionT.fail
                            | _ => OptionT.fail
                        | _ => OptionT.fail
                    | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.hasAttr e F) (PathSet.somepaths (List.cons (CedarExpr.getAttr u_4 u_5) (List.nil))) =>
              match DecOpt.decOpt (BEq.beq u_4 e) initSize with
              | Option.some Bool.true =>
                match DecOpt.decOpt (BEq.beq u_5 F) initSize with
                | Option.some Bool.true => do
                  let x ← Enum.enum;
                  do
                    let TE ← aux_enum initSize size' a_1_1_1 v_1_1_1 (Prod.mk e x);
                    do
                      let ets ← Enum.enum;
                      do
                        let ns ← EnumSizedSuchThat.enumSizedST (fun ns => DefinedEntities ets ns) initSize;
                        do
                          let acts ← Enum.enum;
                          do
                            let R ← Enum.enum;
                            match
                                DecOpt.decOpt (Eq v_1_1_1 (Environment.MkEnvironment (Schema.MkSchema ets acts) R))
                                  initSize with
                              | Option.some Bool.true => do
                                let T ← Enum.enum;
                                match
                                    DecOpt.decOpt (BindAttrType ns (Prod.mk TE (Prod.mk F (Bool.true))) T) initSize with
                                  | Option.some Bool.true => return CedarType.boolType (BoolType.anyBool)
                                  | _ => OptionT.fail
                              | _ => OptionT.fail
                | _ => OptionT.fail
              | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.hasAttr e F) (PathSet.somepaths (List.cons (CedarExpr.getAttr u_4 u_5) (List.nil))) =>
              match DecOpt.decOpt (BEq.beq u_4 e) initSize with
              | Option.some Bool.true =>
                match DecOpt.decOpt (BEq.beq u_5 F) initSize with
                | Option.some Bool.true => do
                  let x ← Enum.enum;
                  do
                    let TE ← aux_enum initSize size' a_1_1_1 v_1_1_1 (Prod.mk e x);
                    do
                      let ets ← Enum.enum;
                      do
                        let ns ← EnumSizedSuchThat.enumSizedST (fun ns => DefinedEntities ets ns) initSize;
                        do
                          let acts ← Enum.enum;
                          do
                            let R ← Enum.enum;
                            match
                                DecOpt.decOpt (Eq v_1_1_1 (Environment.MkEnvironment (Schema.MkSchema ets acts) R))
                                  initSize with
                              | Option.some Bool.true => do
                                let T ← Enum.enum;
                                match
                                    DecOpt.decOpt (BindAttrType ns (Prod.mk TE (Prod.mk F (Bool.false))) T)
                                      initSize with
                                  | Option.some Bool.true => return CedarType.boolType (BoolType.tt)
                                  | _ => OptionT.fail
                              | _ => OptionT.fail
                | _ => OptionT.fail
              | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.getAttr e F) (PathSet.somepaths (List.nil)) =>
              match DecOpt.decOpt (Eq (validPathExpr (CedarExpr.getAttr e F) a_1_1_1) (Bool.true)) initSize with
              | Option.some Bool.true => do
                let x ← Enum.enum;
                match DecOpt.decOpt (Eq (validPathExpr (CedarExpr.getAttr e F) a_1_1_1) (Bool.true)) initSize with
                  | Option.some Bool.true => do
                    let TE ← aux_enum initSize size' a_1_1_1 v_1_1_1 (Prod.mk e x);
                    do
                      let ets ← Enum.enum;
                      do
                        let ns ← EnumSizedSuchThat.enumSizedST (fun ns => DefinedEntities ets ns) initSize;
                        do
                          let acts ← Enum.enum;
                          do
                            let R ← Enum.enum;
                            match
                                DecOpt.decOpt (Eq v_1_1_1 (Environment.MkEnvironment (Schema.MkSchema ets acts) R))
                                  initSize with
                              | Option.some Bool.true => do
                                let TE_1 ← Enum.enum;
                                match
                                    DecOpt.decOpt (BindAttrType ns (Prod.mk TE (Prod.mk F (Bool.true))) TE_1)
                                      initSize with
                                  | Option.some Bool.true => return TE_1
                                  | _ => OptionT.fail
                              | _ => OptionT.fail
                  | _ => OptionT.fail
              | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.getAttr e F) (PathSet.somepaths (List.nil)) => do
              let x ← Enum.enum;
              do
                let TE ← aux_enum initSize size' a_1_1_1 v_1_1_1 (Prod.mk e x);
                do
                  let ets ← Enum.enum;
                  do
                    let ns ← EnumSizedSuchThat.enumSizedST (fun ns => DefinedEntities ets ns) initSize;
                    do
                      let acts ← Enum.enum;
                      do
                        let R ← Enum.enum;
                        match
                            DecOpt.decOpt (Eq v_1_1_1 (Environment.MkEnvironment (Schema.MkSchema ets acts) R))
                              initSize with
                          | Option.some Bool.true => do
                            let TE_1 ← Enum.enum;
                            match
                                DecOpt.decOpt (BindAttrType ns (Prod.mk TE (Prod.mk F (Bool.false))) TE_1) initSize with
                              | Option.some Bool.true => return TE_1
                              | _ => OptionT.fail
                          | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.hasAttr e fn) (PathSet.somepaths (List.cons (CedarExpr.getAttr u_4 u_5) (List.nil))) =>
              match DecOpt.decOpt (BEq.beq u_5 fn) initSize with
              | Option.some Bool.true =>
                match DecOpt.decOpt (BEq.beq u_4 e) initSize with
                | Option.some Bool.true => do
                  let ets ← Enum.enum;
                  do
                    let n ← Enum.enum;
                    do
                      let T ←
                        EnumSizedSuchThat.enumSizedST
                            (fun T => GetEntityAttr ets (Prod.mk n (Prod.mk fn (Bool.true))) T) initSize;
                      do
                        let acts ← Enum.enum;
                        do
                          let R ← Enum.enum;
                          match
                              DecOpt.decOpt (Eq v_1_1_1 (Environment.MkEnvironment (Schema.MkSchema ets acts) R))
                                initSize with
                            | Option.some Bool.true => do
                              let x ← Enum.enum;
                              match
                                  aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk e x) (CedarType.entityType n) with
                                | Option.some Bool.true => return CedarType.boolType (BoolType.anyBool)
                                | _ => OptionT.fail
                            | _ => OptionT.fail
                | _ => OptionT.fail
              | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.hasAttr e fn) (PathSet.somepaths (List.cons (CedarExpr.getAttr u_4 u_5) (List.nil))) =>
              match DecOpt.decOpt (BEq.beq u_5 fn) initSize with
              | Option.some Bool.true =>
                match DecOpt.decOpt (BEq.beq u_4 e) initSize with
                | Option.some Bool.true => do
                  let ets ← Enum.enum;
                  do
                    let n ← Enum.enum;
                    do
                      let T ←
                        EnumSizedSuchThat.enumSizedST
                            (fun T => GetEntityAttr ets (Prod.mk n (Prod.mk fn (Bool.false))) T) initSize;
                      do
                        let acts ← Enum.enum;
                        do
                          let R ← Enum.enum;
                          match
                              DecOpt.decOpt (Eq v_1_1_1 (Environment.MkEnvironment (Schema.MkSchema ets acts) R))
                                initSize with
                            | Option.some Bool.true => do
                              let x ← Enum.enum;
                              match
                                  aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk e x) (CedarType.entityType n) with
                                | Option.some Bool.true => return CedarType.boolType (BoolType.tt)
                                | _ => OptionT.fail
                            | _ => OptionT.fail
                | _ => OptionT.fail
              | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.getAttr e fn) (PathSet.somepaths (List.nil)) =>
              match DecOpt.decOpt (Eq (validPathExpr (CedarExpr.getAttr e fn) a_1_1_1) (Bool.true)) initSize with
              | Option.some Bool.true => do
                let ets ← Enum.enum;
                do
                  let n ← Enum.enum;
                  match DecOpt.decOpt (Eq (validPathExpr (CedarExpr.getAttr e fn) a_1_1_1) (Bool.true)) initSize with
                    | Option.some Bool.true => do
                      let TE_1 ←
                        EnumSizedSuchThat.enumSizedST
                            (fun TE_1 => GetEntityAttr ets (Prod.mk n (Prod.mk fn (Bool.true))) TE_1) initSize;
                      do
                        let acts ← Enum.enum;
                        do
                          let R ← Enum.enum;
                          match
                              DecOpt.decOpt (Eq v_1_1_1 (Environment.MkEnvironment (Schema.MkSchema ets acts) R))
                                initSize with
                            | Option.some Bool.true => do
                              let x ← Enum.enum;
                              match
                                  aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk e x) (CedarType.entityType n) with
                                | Option.some Bool.true => return TE_1
                                | _ => OptionT.fail
                            | _ => OptionT.fail
                    | _ => OptionT.fail
              | _ => OptionT.fail
            | _ => OptionT.fail,
            match ex_1 with
            | Prod.mk (CedarExpr.getAttr e fn) (PathSet.somepaths (List.nil)) => do
              let ets ← Enum.enum;
              do
                let n ← Enum.enum;
                do
                  let TE_1 ←
                    EnumSizedSuchThat.enumSizedST
                        (fun TE_1 => GetEntityAttr ets (Prod.mk n (Prod.mk fn (Bool.false))) TE_1) initSize;
                  do
                    let acts ← Enum.enum;
                    do
                      let R ← Enum.enum;
                      match
                          DecOpt.decOpt (Eq v_1_1_1 (Environment.MkEnvironment (Schema.MkSchema ets acts) R))
                            initSize with
                        | Option.some Bool.true => do
                          let x ← Enum.enum;
                          match
                              aux_dec initSize size' a_1_1_1 v_1_1_1 (Prod.mk e x) (CedarType.entityType n)
                                 with
                            | Option.some Bool.true => return TE_1
                            | _ => OptionT.fail
                        | _ => OptionT.fail
            | _ => OptionT.fail])
end

instance : DecOpt (HasType a_1 v_1 e_1 t_1) where
  decOpt :=
    fun size => aux_dec size size a_1 v_1 e_1 t_1
instance : EnumSizedSuchThat CedarType (fun TE_1 => HasType a_1_1_1 v_1_1_1 ex_1 TE_1) where
  enumSizedST :=
    fun size => aux_enum size size a_1_1_1 v_1_1_1 ex_1
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

#derive_generator (fun (t : _) => HasType a v ex t)

#derive_generator (fun (ns_1 : _) => WfRecordType ns_1 r)

#derive_generator (fun (ns : _) => BindAttrType ns TE t_1)

#derive_generator (fun (E : _) => LookupEntityAttr E (fn, b) t_1_1)

#derive_generator (fun (ets : _) => GetEntityAttr ets n t_1)

#derive_generator (fun (ex : (CedarExpr × PathSet)) => HasType a v ex t)

#derive_generator (fun (rs_1_1 : _) => ActionToRequestTypes uid_1 p rs c l_1_1 rs_1_1)

#derive_generator (fun (rs_1 : _) => ActionSchemaEntryToRequestTypes uid a l_1 rs_1)

#derive_generator (fun (rs : _) => ActionSchemaToRequestTypes acts l rs)

#derive_generator (fun (es : _) => SchemaToEnvironments (.MkSchema ets acts) reqs es)
