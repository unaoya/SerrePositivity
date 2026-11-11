module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.StrictLeftFibrationSections
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.WeightedNerveParameterFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NerveTensor

/-!
概要：strict 図式の相対切断を、その共同 weighted nerve へ全パラメータで同時に評価する。
方針：元の係数評価を weighted nerve に写し、追加パラメータのテンソル写像と合成する。
規約：元の添字と底の射をともに保持する。頂点だけの評価に置き換えない。
使われ方：共同 weighted 分類と strict 分類像の全単体上の比較。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {I : Type u} [Category.{u} I] {B A : SSet.{u}}
  (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B) (a : A ⟶ B)

instance leftFibrationDiagramProjection_leftFibration (i : I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.leftFibrationDiagramProjection F).app i) := (F.obj i).property

/-- 元の strict left fibration 図式の共同 weighted 射影。 -/
def leftFibrationWeightedProjection : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.leftFibrationTotalDiagram F) ⟶
    B ⊗ nerve I := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameterProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.leftFibrationDiagramProjection F)

instance leftFibrationWeightedProjection_leftFibration :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (leftFibrationWeightedProjection F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameterProjection_leftFibration _

/-- 同じ相対切断の評価は、元の底の射 a を厳密に保つ。 -/
lemma strictLeftSectionEvaluation_projection (i : I) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictLeftSectionEvaluation F a).app i ≫ (F.obj i).val.hom =
      snd ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictLeftFibrationSectionDiagram F a).obj i).obj A ≫ a := by
  change (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace (F.obj i).val.hom a) A).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (p := (F.obj i).val.hom) (a := a) (𝟙 _) ≫
      (F.obj i).val.hom = snd (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace (F.obj i).val.hom a) A ≫ a
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_projection, braiding_hom_fst_assoc]

/-- 相対切断の全図式を、その元の共同 weighted nerve に同時に評価する射。 -/
def weightedLeftSectionEvaluation :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictLeftFibrationSectionDiagram F a ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) ⊗ A ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.leftFibrationTotalDiagram F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTensorMap _ A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictLeftSectionEvaluation F a)

/-- 同じ全評価は元の添字の射影を厳密に保つ。 -/
lemma weightedLeftSectionEvaluation_index :
    weightedLeftSectionEvaluation F a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.leftFibrationTotalDiagram F) =
      fst _ A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictLeftFibrationSectionDiagram F a ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) := by
  rw [weightedLeftSectionEvaluation, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveMap_projection,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.weightedNerveTensorMap_projection]

/-- 同じ全評価の底パラメータは、元の A の単体を元の a で写したもの。 -/
lemma weightedLeftSectionEvaluation_parameter :
    weightedLeftSectionEvaluation F a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameter (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.leftFibrationDiagramProjection F) =
      snd _ A ≫ a := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨σ, τ⟩, t⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶
    σ ⋙ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictLeftFibrationSectionDiagram F a ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) at τ
  change SSet.yonedaEquiv
    (lift (τ.app (Fin.last n))
      (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n n _) ≫ SSet.yonedaEquiv.symm t) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictLeftSectionEvaluation F a).app (σ.obj (Fin.last n)) ≫
      (F.obj (σ.obj (Fin.last n))).val.hom) = a.app _ t
  rw [strictLeftSectionEvaluation_projection, ← Category.assoc]
  have hs := lift_snd (τ.app (Fin.last n))
    (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n n le_rfl) ≫ SSet.yonedaEquiv.symm t)
  refine (congrArg (fun f : (Δ[n] : SSet.{u}) ⟶ A ↦ SSet.yonedaEquiv (f ≫ a)) hs).trans ?_
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion_id]
  change SSet.yonedaEquiv (((𝟙 (Δ[n] : SSet.{u})) ≫ SSet.yonedaEquiv.symm t) ≫ a) = _
  rw [Category.id_comp, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]

/-- 全相対切断の評価は、元の積上の共同射影を厳密に保つ。 -/
lemma weightedLeftSectionEvaluation_over_product :
    weightedLeftSectionEvaluation F a ≫ leftFibrationWeightedProjection F =
      lift (snd _ A ≫ a) (fst _ A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictLeftFibrationSectionDiagram F a ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, leftFibrationWeightedProjection, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameterProjection,
      lift_fst, weightedLeftSectionEvaluation_parameter, lift_fst]
  · rw [Category.assoc, leftFibrationWeightedProjection, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameterProjection,
      lift_snd, weightedLeftSectionEvaluation_index, lift_snd]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
