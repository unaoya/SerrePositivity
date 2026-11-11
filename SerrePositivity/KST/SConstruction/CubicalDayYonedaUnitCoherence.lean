module
public import SerrePositivity.KST.SConstruction.CubicalDayYonedaData
public import SerrePositivity.KST.SConstruction.CubicalDayStructuralCells

/-! # 元の Yoneda 単位比較の左右の整合性
概要：元の表現可能単位の逆比較は、Day と具体的連結積の左右単位を保持する。
方針：Day 単位の元の生成 cell を固定し、元の表現可能立方体の恒等 cell で判定する。
規約：元の単位比較と左右の構造射を変更しない。使われ方：強モノイダル Yoneda。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite

/-- 元の左単位の逆比較の後に Day 左単位を合成すると恒等を回収する。 -/
lemma cubicalDayYoneda_leftUnit_retraction (c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    cubicalYoneda.{u}.map (concreteCubeLeftUnitor c).inv ≫
        cubicalDayCubeInclusion (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0) c ≫
          cubicalDayTensorMap cubicalDayUnitInclusion (𝟙 (cubicalYoneda.{u}.obj c)) ≫
            (λ_ (DayFunctor.mk (cubicalYoneda.{u}.obj c))).hom.natTrans =
      𝟙 (cubicalYoneda.{u}.obj c) := by
  apply uliftYonedaEquiv.injective
  change (λ_ (DayFunctor.mk (cubicalYoneda.{u}.obj c))).hom.natTrans.app (op c)
      ((cubicalDayTensorMap cubicalDayUnitInclusion (𝟙 (cubicalYoneda.{u}.obj c))).app (op c)
        ((cubicalDayCubeInclusion (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0) c).app (op c)
          (ULift.up (concreteCubeLeftUnitor c).inv))) = ULift.up (𝟙 c)
  change (λ_ (DayFunctor.mk (cubicalYoneda.{u}.obj c))).hom.natTrans.app (op c)
      ((cubicalDayTensorMap cubicalDayUnitInclusion (𝟙 (cubicalYoneda.{u}.obj c))).app (op c)
        ((cubicalDayTensor (cubicalYoneda.{u}.obj (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0))
          (cubicalYoneda.{u}.obj c)).map
          (concreteCubeLeftUnitor c).inv.op
          (cubicalDayTensorCell (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0) c (ULift.up (𝟙 _)) (ULift.up (𝟙 c))))) = _
  erw [cubicalNatTrans_restrict
    (cubicalDayTensorMap cubicalDayUnitInclusion (𝟙 (cubicalYoneda.{u}.obj c)))
    (concreteCubeLeftUnitor c).inv]
  erw [cubicalDayTensorMap_cell cubicalDayUnitInclusion (𝟙 (cubicalYoneda.{u}.obj c))
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0) c]
  erw [cubicalDayUnitInclusion_identity]
  erw [cubicalNatTrans_restrict
    (λ_ (DayFunctor.mk (cubicalYoneda.{u}.obj c))).hom.natTrans
    (concreteCubeLeftUnitor c).inv]
  erw [cubicalDayLeftUnitor_cell (cubicalYoneda.{u}.obj c) c]
  change ULift.up ((concreteCubeLeftUnitor c).inv ≫ (concreteCubeLeftUnitor c).hom) = _
  rw [Iso.inv_hom_id]

/-- 元の右単位の逆比較の後に Day 右単位を合成すると恒等を回収する。 -/
lemma cubicalDayYoneda_rightUnit_retraction (c : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    cubicalYoneda.{u}.map (concreteCubeRightUnitor c).inv ≫
        cubicalDayCubeInclusion c (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0) ≫
          cubicalDayTensorMap (𝟙 (cubicalYoneda.{u}.obj c)) cubicalDayUnitInclusion ≫
            (ρ_ (DayFunctor.mk (cubicalYoneda.{u}.obj c))).hom.natTrans =
      𝟙 (cubicalYoneda.{u}.obj c) := by
  apply uliftYonedaEquiv.injective
  change (ρ_ (DayFunctor.mk (cubicalYoneda.{u}.obj c))).hom.natTrans.app (op c)
      ((cubicalDayTensorMap (𝟙 (cubicalYoneda.{u}.obj c)) cubicalDayUnitInclusion).app (op c)
        ((cubicalDayCubeInclusion c (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0)).app (op c)
          (ULift.up (concreteCubeRightUnitor c).inv))) = ULift.up (𝟙 c)
  change (ρ_ (DayFunctor.mk (cubicalYoneda.{u}.obj c))).hom.natTrans.app (op c)
      ((cubicalDayTensorMap (𝟙 (cubicalYoneda.{u}.obj c)) cubicalDayUnitInclusion).app (op c)
        ((cubicalDayTensor (cubicalYoneda.{u}.obj c)
          (cubicalYoneda.{u}.obj (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0))).map
          (concreteCubeRightUnitor c).inv.op
          (cubicalDayTensorCell c (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0) (ULift.up (𝟙 c)) (ULift.up (𝟙 _))))) = _
  erw [cubicalNatTrans_restrict
    (cubicalDayTensorMap (𝟙 (cubicalYoneda.{u}.obj c)) cubicalDayUnitInclusion)
    (concreteCubeRightUnitor c).inv]
  erw [cubicalDayTensorMap_cell (𝟙 (cubicalYoneda.{u}.obj c)) cubicalDayUnitInclusion
    c (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0)]
  erw [cubicalDayUnitInclusion_identity]
  erw [cubicalNatTrans_restrict
    (ρ_ (DayFunctor.mk (cubicalYoneda.{u}.obj c))).hom.natTrans
    (concreteCubeRightUnitor c).inv]
  erw [cubicalDayRightUnitor_cell (cubicalYoneda.{u}.obj c) c]
  change ULift.up ((concreteCubeRightUnitor c).inv ≫ (concreteCubeRightUnitor c).hom) = _
  rw [Iso.inv_hom_id]

end SerrePositivity.KST.SConstruction
