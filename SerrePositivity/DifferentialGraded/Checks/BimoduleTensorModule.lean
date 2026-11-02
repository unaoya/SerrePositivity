module
public import SerrePositivity.DifferentialGraded.Bimodule.Tensor
public import Mathlib.Data.ZMod.Basic

/-! # 積dg圏上の加群から主bimodule圏への射・評価比較の受入監査

## 概要
積dg圏上の加群から主bimodule圏への射・評価比較の受入監査。

## 方針
既存の例・型照合・公理監査集合を保持し、証明済みの個別契約を検査する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。対応する一般APIの再現可能な検査入口。中断した一般経路を再開する際にも同じ対象を再実行できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory Opposite
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

example : Small.{u} (DGTensorCategory A Bᵒᵖ C) := inferInstance
example : (BimoduleTensorModule.functor A B C).Faithful := inferInstance
example : (BimoduleTensorModule.functor A B C).EssSurj := inferInstance

example (b : B) (c : C) :
    BimoduleTensorModule.functor A B C ⋙ BimoduleCategory.valueEvaluation A B C b c ≅
      leftModuleEvaluation A (DGTensorCategory A Bᵒᵖ C) (op b, c) :=
  BimoduleTensorModule.evaluationIso A B C b c

example (M : BimoduleCategory A B C) :
    (BimoduleTensorModule.functor A B C).obj (BimoduleTensorModule.objectPreimage A B C M) ≅ M :=
  BimoduleTensorModule.objectPreimageIso A B C M

example {M N : BimoduleTensorModuleCategory A B C} (f : M ⟶ N) :
    BimoduleCategory.quasiIso A B C ((BimoduleTensorModule.functor A B C).map f) ↔
      leftModuleQuasiIso A (DGTensorCategory A Bᵒᵖ C) f :=
  BimoduleTensorModule.functor_quasiIso_iff A B C f

example {M N P : BimoduleTensorModuleCategory A B C} (f : M ⟶ N) (g : N ⟶ P) :
    (BimoduleTensorModule.functor A B C).map (f ≫ g) =
      (BimoduleTensorModule.functor A B C).map f ≫ (BimoduleTensorModule.functor A B C).map g :=
  (BimoduleTensorModule.functor A B C).map_comp f g

example (B : Type v) (C : Type w) [DGCategory (ZMod 2) B] [DGCategory (ZMod 2) C]
    [Small.{0} B] [Small.{0} C] : (BimoduleTensorModule.functor (ZMod 2) B C).Faithful :=
  inferInstance

#print axioms SerrePositivity.DifferentialGraded.dgTensorSmall
#print axioms SerrePositivity.DifferentialGraded.leftModuleMorphism_naturality
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensorModuleCategory
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensorModule.underlying
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensorModule.rightMap
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensorModule.rightMap_component
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensorModule.rightMap_left_naturality
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensorModule.map
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensorModule.map_value
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensorModule.map_id
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensorModule.map_comp
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensorModule.functor
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensorModule.functor_map_value
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensorModule.evaluationIso
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensorModule.faithful
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensorModule.objectPreimage
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensorModule.objectPreimageIso
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensorModule.essSurj
#print axioms SerrePositivity.DifferentialGraded.BimoduleTensorModule.functor_quasiIso_iff
