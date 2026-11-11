module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.SectionProductReplacementMap

/-!
概要：全単体の切断の大域評価は、元の底の初頂点写像と元の添字の積を厳密に保つ。
方針：始点係数の底への合成と、taut scaffold の元のパラメータ公式を照合する。
規約：元の共同 weighted 射影へ重なる同じ大域射を保持する。
使われ方：全単体上の分類比較を元の積上の left scaffold 比較へ戻す。

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
variable {I : Type u} [Category.{u} I] {B : SSet.{u}} (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B)

/-- 同じ始点係数の評価は、元の全射列の初頂点座標を被覆する。 -/
lemma sectionProductReplacementCoefficient_projection {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementSimplex
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictLeftTransportSectionDiagram F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.sectionProductReplacementCoefficient F s ≫ (F.obj (s.1.obj 0).1).val.hom =
      SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMorphism
        (s.1 ⋙ CategoryTheory.Prod.snd I (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B))) ≫
          SSet.yonedaEquiv.symm (s.1.obj 0).2.objDown.val := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.sectionProductReplacementCoefficient, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_projection, ← Category.assoc, lift_fst]
  rfl

/-- 全単体の添字と元の添字の積から、元の共同底への同じ初頂点写像。 -/
def sectionProductBaseMap (I : Type u) [Category.{u} I] (B : SSet.{u}) :
    nerve (I × _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B) ⟶ B ⊗ nerve I :=
  lift (nerveMap (CategoryTheory.Prod.snd I (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B)) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B)
    (nerveMap (CategoryTheory.Prod.fst I (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B)))

/-- 同じ大域評価の底パラメータは、元の全単体の初頂点写像。 -/
lemma sectionProductWeightedEvaluation_parameter :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.sectionProductWeightedEvaluation F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameter (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.leftFibrationDiagramProjection F) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictLeftTransportSectionDiagram F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) ≫
        nerveMap (CategoryTheory.Prod.snd I (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B)) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  have h := congrArg SSet.yonedaEquiv
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.tautScaffold_parameter (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.leftFibrationDiagramProjection F)
      ⟨s.1 ⋙ CategoryTheory.Prod.fst I (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B),
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.sectionProductReplacementCoefficient F s⟩)
  simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at h
  change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexSimplex
    (s.1 ⋙ CategoryTheory.Prod.snd I (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B))
  calc
    _ = SSet.yonedaEquiv
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.sectionProductReplacementCoefficient F s ≫ (F.obj (s.1.obj 0).1).val.hom) := h
    _ = _ := by
      rw [sectionProductReplacementCoefficient_projection, ← SSet.yonedaEquiv_naturality,
        Equiv.apply_symm_apply]
      rfl

/-- 元の全切断の大域評価は、元の積上の共同射影へ厳密に重なる。 -/
lemma sectionProductWeightedEvaluation_over_product :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.sectionProductWeightedEvaluation F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.leftFibrationWeightedProjection F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictLeftTransportSectionDiagram F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) ≫
        sectionProductBaseMap I B := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.leftFibrationWeightedProjection, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameterProjection,
      sectionProductBaseMap, lift_fst]
    exact sectionProductWeightedEvaluation_parameter F
  · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.leftFibrationWeightedProjection, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.weightedNerveParameterProjection,
      sectionProductBaseMap, lift_snd]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.sectionProductWeightedEvaluation_index F

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
