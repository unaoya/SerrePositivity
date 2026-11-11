module
public import SerrePositivity.KST.SConstruction.CubicalDayYonedaData
public import SerrePositivity.KST.SConstruction.CubicalDayStructuralCells

/-! # 元の Yoneda tensor 比較の結合整合性
概要：元の表現可能 tensor の逆比較は、Day と具体的連結積の結合同型を保持する。
方針：元の連結した表現可能立方体の恒等 cell を評価し、構造 cell の式を使う。
規約：既存の両逆律を持つ同じ比較射を使う。使われ方：強モノイダル Yoneda。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite

/-- 元の表現可能 tensor の逆比較と、元の両結合同型の可換性。 -/
lemma cubicalDayCubeInclusion_associativity (c d e : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    cubicalDayCubeInclusion.{u} (concreteCubeTensorObj c d) e ≫
        cubicalDayTensorMap (cubicalDayCubeInclusion c d) (𝟙 (cubicalYoneda.{u}.obj e)) ≫
          (α_ (DayFunctor.mk (cubicalYoneda.{u}.obj c)) (DayFunctor.mk (cubicalYoneda.{u}.obj d))
            (DayFunctor.mk (cubicalYoneda.{u}.obj e))).hom.natTrans =
      cubicalYoneda.{u}.map (concreteCubeAssociator c d e).hom ≫
        cubicalDayCubeInclusion c (concreteCubeTensorObj d e) ≫
          cubicalDayTensorMap (𝟙 (cubicalYoneda.{u}.obj c)) (cubicalDayCubeInclusion d e) := by
  apply uliftYonedaEquiv.injective
  change (α_ (DayFunctor.mk (cubicalYoneda.{u}.obj c)) (DayFunctor.mk (cubicalYoneda.{u}.obj d))
      (DayFunctor.mk (cubicalYoneda.{u}.obj e))).hom.natTrans.app
      (op (concreteCubeTensorObj (concreteCubeTensorObj c d) e))
      ((cubicalDayTensorMap (cubicalDayCubeInclusion c d) (𝟙 (cubicalYoneda.{u}.obj e))).app
        (op (concreteCubeTensorObj (concreteCubeTensorObj c d) e))
        ((cubicalDayCubeInclusion (concreteCubeTensorObj c d) e).app
          (op (concreteCubeTensorObj (concreteCubeTensorObj c d) e)) (ULift.up (𝟙 _)))) =
    (cubicalDayTensorMap (𝟙 (cubicalYoneda.{u}.obj c)) (cubicalDayCubeInclusion d e)).app
      (op (concreteCubeTensorObj (concreteCubeTensorObj c d) e))
      ((cubicalDayCubeInclusion c (concreteCubeTensorObj d e)).app
        (op (concreteCubeTensorObj (concreteCubeTensorObj c d) e))
        (ULift.up (concreteCubeAssociator c d e).hom))
  erw [cubicalDayCubeInclusion_identity (concreteCubeTensorObj c d) e]
  erw [cubicalDayTensorMap_cell (cubicalDayCubeInclusion c d)
    (𝟙 (cubicalYoneda.{u}.obj e)) (concreteCubeTensorObj c d) e]
  erw [cubicalDayCubeInclusion_identity c d]
  erw [cubicalDayAssociator_cell (cubicalYoneda.{u}.obj c) (cubicalYoneda.obj d)
    (cubicalYoneda.obj e) c d e]
  change (cubicalDayTensor (cubicalYoneda.{u}.obj c)
      (cubicalDayTensor (cubicalYoneda.{u}.obj d) (cubicalYoneda.{u}.obj e))).map
      (concreteCubeAssociator c d e).hom.op
      (cubicalDayTensorCell c (concreteCubeTensorObj d e) (ULift.up (𝟙 c))
        (cubicalDayTensorCell d e (ULift.up (𝟙 d)) (ULift.up (𝟙 e)))) =
    (cubicalDayTensorMap (𝟙 (cubicalYoneda.{u}.obj c)) (cubicalDayCubeInclusion d e)).app
      (op (concreteCubeTensorObj (concreteCubeTensorObj c d) e))
      ((cubicalDayTensor (cubicalYoneda.{u}.obj c)
        (cubicalYoneda.{u}.obj (concreteCubeTensorObj d e))).map
        (concreteCubeAssociator c d e).hom.op
        (cubicalDayTensorCell c (concreteCubeTensorObj d e)
          (ULift.up (𝟙 c)) (ULift.up (𝟙 _))))
  erw [cubicalNatTrans_restrict
    (cubicalDayTensorMap (𝟙 (cubicalYoneda.{u}.obj c)) (cubicalDayCubeInclusion d e))
    (concreteCubeAssociator c d e).hom]
  erw [cubicalDayTensorMap_cell (𝟙 (cubicalYoneda.{u}.obj c)) (cubicalDayCubeInclusion d e)
    c (concreteCubeTensorObj d e)]
  erw [cubicalDayCubeInclusion_identity d e]
  rfl

end SerrePositivity.KST.SConstruction
