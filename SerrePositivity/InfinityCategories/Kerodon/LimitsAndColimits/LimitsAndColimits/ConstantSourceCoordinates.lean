module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.ConstantSourceComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ConstantDiagramTransportWitness

/-!
概要：定値始域の二種類の直積座標を、全評価の合成で厳密に照合する。
方針：引き戻しの二射影へ移し、元の底と fiber の座標をそれぞれ計算する。
規約：元の底と全高次パラメータを保持する。
使われ方：相対合成の全切断による評価の計算。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 定値全空間の始域座標の逆から fiber を取ると、元の第二射影。 -/
lemma constantSourceOverIso_inv_fiber (B : SSet.{u + 1}) (x : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.constantUnstraighteningSourceOverIso B x).inv.left ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantUnstraighteningFiberProjection B x = snd B (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection x) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection x
  rw [Category.assoc]
  change _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantPullbackFiberIso _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection x).hom ≫
    fst _ B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection x = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantPullbackFiberIso_fst_ι]
  change _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.tensorToPullbackConstant _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection x B ≫ pullback.fst _ _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.tensorToPullbackConstant, pullback.lift_fst]

/-- 元の定値全空間の fiber 評価を再構成すると、同じ底上の直積射になる。 -/
lemma constantSourceCoordinates {B T : SSet.{u + 1}}
    (x y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌)
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection x ⊗ T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection y) :
    (α_ B (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection x) T).inv ≫
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.constantUnstraighteningSourceOverIso B x).inv.left ▷ T) ≫
          lift ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantUnstraighteningFiberProjection B x ▷ T) ≫ f)
            (fst (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening (SSet.const x : B ⟶ _)) T ≫
              _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (SSet.const x : B ⟶ _)) ≫
                (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantPullbackFiberIso _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection y).inv =
      (B ◁ f) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.constantUnstraighteningSourceOverIso B y).inv.left := by
  apply pullback.hom_ext
  · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantPullbackFiberIso_inv_fst, lift_fst_assoc]
    change _ = (B ◁ f) ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.tensorToPullbackConstant _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection y B ≫ _
    rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.tensorToPullbackConstant, pullback.lift_fst]
    rw [← Category.assoc ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.constantUnstraighteningSourceOverIso B x).inv.left ▷ T),
      ← comp_whiskerRight, constantSourceOverIso_inv_fiber]
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨b, v, t⟩
    rfl
  · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantPullbackFiberIso_inv_snd, lift_snd]
    change _ = (B ◁ f) ≫ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.tensorToPullbackConstant _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection y B ≫ _
    rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Pullbacks.tensorToPullbackConstant, pullback.lift_snd]
    have hb : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.constantUnstraighteningSourceOverIso B x).inv.left ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection (SSet.const x : B ⟶ _) =
          fst B (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection x) :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.constantUnstraighteningSourceOverIso B x).inv.w
    rw [← Category.assoc ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.constantUnstraighteningSourceOverIso B x).inv.left ▷ T),
      whiskerRight_fst, Category.assoc, hb]
    rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
