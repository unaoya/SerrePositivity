module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoYonedaFullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FullyFaithfulLimitCreation
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseLimits

/-!
概要：元の全 Hom 図式の表現可能な極限から元の余極限の存在を回収する。
方針：充満忠実な co-Yoneda 像の極限を持ち上げ、宇宙変更と反転を戻す。
規約：表現可能性は全係数に自然な頂点同型で与える。
使われ方：Ind 延長と幾何学的実現による局所 Kan 余極限の構成。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：全 co-Yoneda 図式の極限頂点が表現可能なら元の図式の余極限が存在する。
方針：同じ反対図式の持ち上げを充満忠実性で戻し、元の宇宙へ降ろす。
規約：元の任意の形状と全係数自然性を保持する。
使われ方：filtered・geometric な計算による重み付き余極限の存在。 -/
lemma hasColimit_of_coyoneda_limit_representable
    {K C : SSet.{u}} [Quasicategory C] (p : K ⟶ C)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map p) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap C)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c)
    (hrep : ∃ z : C _⦋0⦌, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant z)) c.vertex)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanHasColimit_iff_hasLimit_op p).mpr
  apply (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.hasLimit_iff_ulift (SSet.opFunctor.map p)).mpr
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.hasLimit_of_fullyFaithful_image_limit_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap C)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coyonedaInfinityMap_isFullyFaithful C)
    ((SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map p)) c hc
  obtain ⟨z, ⟨e⟩⟩ := hrep
  exact ⟨ULift.up (SSet.opObjEquiv.symm z),
    ⟨eqToIso (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap_vertex z)) ≪≫ e⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
