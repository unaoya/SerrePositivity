module
public import SerrePositivity.KST.SConstruction.CubicalDayTensorLaws
public import SerrePositivity.KST.SConstruction.CubicalDayUnit

/-! # 元の連結 cell に対する Day 構造射の評価
概要：Day 結合同型と左右単位の元の cell 上の評価を回収する。
方針：左 Kan 延長の単位との構造可換式を、Type の元で評価する。
規約：具体的立方体の元の結合・単位射を保持する。使われ方：Yoneda 比較の coherence。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite
open LawfulDayConvolutionMonoidalCategoryStruct

/-- 元の三つの連結 cell に対する Day 結合同型の評価。 -/
lemma cubicalDayAssociator_cell (K L M : CubicalSet.{u}) (a b c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube)
    (x : K.obj (op a)) (y : L.obj (op b)) (z : M.obj (op c)) :
    (α_ (DayFunctor.mk K) (DayFunctor.mk L) (DayFunctor.mk M)).hom.natTrans.app
        (op (concreteCubeTensorObj (concreteCubeTensorObj a b) c))
        (cubicalDayTensorCell (concreteCubeTensorObj a b) c
          (cubicalDayTensorCell a b x y) z) =
      (cubicalDayTensor K (cubicalDayTensor L M)).map (concreteCubeAssociator a b c).hom.op
        (cubicalDayTensorCell a (concreteCubeTensorObj b c) x
          (cubicalDayTensorCell b c y z)) := by
  have h := associator_hom_unit_unit (C := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ) (Type u)
    (DayFunctor.mk K) (DayFunctor.mk L) (DayFunctor.mk M) (op a) (op b) (op c)
  exact congrArg (fun t => t ((x, y), z)) h

/-- 元の単位生成 cell と任意の cell に対する Day 左単位の評価。 -/
lemma cubicalDayLeftUnitor_cell (K : CubicalSet.{u}) (c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube)
    (x : K.obj (op c)) :
    (λ_ (DayFunctor.mk K)).hom.natTrans.app
        (op (concreteCubeTensorObj (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0) c))
        (cubicalDayTensorCell (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0) c cubicalDayUnitCell x) =
      K.map (concreteCubeLeftUnitor c).hom.op x := by
  have h := leftUnitor_hom_unit_app (C := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ) (Type u) (DayFunctor.mk K) (op c)
  exact congrArg (fun t => t (PUnit.unit, x)) h

/-- 元の任意の cell と単位生成 cell に対する Day 右単位の評価。 -/
lemma cubicalDayRightUnitor_cell (K : CubicalSet.{u}) (c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube)
    (x : K.obj (op c)) :
    (ρ_ (DayFunctor.mk K)).hom.natTrans.app
        (op (concreteCubeTensorObj c (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0)))
        (cubicalDayTensorCell c (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0) x cubicalDayUnitCell) =
      K.map (concreteCubeRightUnitor c).hom.op x := by
  have h := rightUnitor_hom_unit_app (C := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCubeᵒᵖ) (Type u) (DayFunctor.mk K) (op c)
  exact congrArg (fun t => t (x, PUnit.unit)) h

end SerrePositivity.KST.SConstruction
