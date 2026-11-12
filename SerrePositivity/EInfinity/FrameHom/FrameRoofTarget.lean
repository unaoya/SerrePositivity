module

public import SerrePositivity.EInfinity.FrameHom.FrameRoofSource
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofLocallyConstantPullback
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RightFibrationContractible

/-!
# 元の frame の実屋根標的と次数射影

概要：実屋根標的を元の slice 引き戻しのまま扱い、右ファイブレーション性を供給する。
方針：元の射影を基底変換し、全 frame 射の反転から左側の充填性も得る。
規約：元の指定点・次数・全高次単体を保持し、頂点集合へ置き換えない。
使われ方：実屋根比較の Quillen A の全 slice の計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom.FrameArrows
open CategoryTheory Limits Opposite SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C) (Y : C)
  {E : SSet.{u}} (q : nerve C ⟶ E)

abbrev roofTarget := pullback
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y) ≫ q)) (nerveMap A ≫ q)
abbrev roofTargetProjection : roofTarget A Y q ⟶ nerve I := pullback.snd _ _

instance roofTargetProjection_rightFibration [SSet.Quasicategory E] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (roofTargetProjection A Y q) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.rightFibration_pullback_snd _ _

instance roofTarget_quasicategory [SSet.Quasicategory E] :
    SSet.Quasicategory (roofTarget A Y q) :=
  SSet.quasicategory_of_innerFibration (roofTargetProjection A Y q)

lemma roofTargetProjection_leftFibration [SSet.Quasicategory E]
    (hA : ∀ {i j : I} (f : i ⟶ j),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((nerve.edgeMk (A.map f)).map q).toTruncated) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (roofTargetProjection A Y q) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofRightFibration_pullback_leftFibration_of_inverts
  intro s
  obtain ⟨i, j, f, rfl⟩ := ComposableArrows.mk₁_surjective s
  have he : (nerveMap A ≫ q).app (op ⦋1⦌) (ComposableArrows.mk₁ f) =
      ((nerve.edgeMk (A.map f)).map q).edge := by
    rw [NatTrans.comp_app_apply, nerveMap_app_mk₁]
    rfl
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex _)
    (f := ((nerve.edgeMk (A.map f)).map q).toTruncated) he).mpr (hA f)

def roofTargetDegree (b : (roofTarget A Y q) _⦋0⦌) : I :=
  ((roofTargetProjection A Y q).app (op ⦋0⦌) b).obj 0

lemma roofTargetDegree_vertex (b : (roofTarget A Y q) _⦋0⦌) :
    (roofTargetProjection A Y q).app (op ⦋0⦌) b =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (roofTargetDegree A Y q b) := ComposableArrows.ext₀ rfl

lemma roofTargetPoint_projection (b : (roofTarget A Y q) _⦋0⦌) :
    SSet.yonedaEquiv.symm b ≫ roofTargetProjection A Y q =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (roofTargetDegree A Y q b)) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact roofTargetDegree_vertex A Y q b

end SerrePositivity.EInfinity.FrameHom.FrameArrows
