module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RepresentedReflectiveUnit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LeftAdjointAllColimitPreservation
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ContravariantContinuity

/-!
概要：反映部分圏上の連続な前層を元の前層圏で表現し、その表現が元の単位を反転する。
方針：reflector の余極限保存で制限し、自由前層圏の表現可能性と指定単位の反転を使う。
規約：表現対象の局所性はここでは結論しない。
使われ方：F1 の前合成比較で局所性を得て元の反映部分圏へ降ろす直前の界面。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：反映上の連続前層の引き戻しは、全単位の元の反対辺を反転する表現を持つ。
方針：同じ reflector による小余極限保存と自由前層の具体的表現を合成する。
規約：元の単位を表す実辺と同じ表現対象を全ての点で保持する。
使われ方：表現可能前層の辺作用と Hom 前合成の比較による局所性判定。 -/
lemma reflectiveContinuous_exists_representation_inverting_units
    {A : SSet.{u}} [Quasicategory A]
    {P : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A) _⦋0⦌ → Prop}
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A) P)
    (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A) P : SSet.{u + 1}).op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.SendsSmallColimitsToLimits F) :
    ∃ z : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A) _⦋0⦌,
      ∃ _h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity z)
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.opFunctor.map r.reflector ≫ F) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseDiagram),
        ∀ (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A) _⦋0⦌)
          (e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A))
            x (r.localization.app _ x)),
          Truncated.HomotopyCategory.homMk e = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitComponent r.unit x →
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u + 1, u + 2} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e)).map
              ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity z))) := by
  have h := hF.precomp_op r.reflector (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.adjunction_preservesSmallColimits r.adjunction)
  obtain ⟨z, ⟨hz⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheaf_isRepresentable_of_sendsSmallColimitsToLimits
    (SSet.opFunctor.map r.reflector ≫ F) h
  exact ⟨z, hz, fun x e he ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.representedReflectiveUnit_inverts_op_edge r F z hz x e he⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
