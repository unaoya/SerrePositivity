module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaSiftedGeneration
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.SiftedColimitPreservation

/-!
概要：指定された元の P_Σ 頂点自身の、元の小さい元の圏上の全密度余錐を固定する。
方針：既存の全密度余錐を同じ頂点関手へ適用し、包含の単射性で指定頂点へ戻す。
規約：元の図式・全余錐・指定頂点を保持。使われ方：標準左 Kan 余錐との厳密な照合。

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
variable {C : SSet.{u}} [Quasicategory C] (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C) _⦋0⦌)

omit [Quasicategory C] in
/-- 元の指定頂点から回収した前層関手も、元の P_Σ 条件を満たす。 -/
lemma sigmaVertexPresheaf_mem : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSigmaPresheaf (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafVertexFunctor v)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafVertexFunctor_vertex v).symm ▸ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaPresheafInfinity_vertex v

/-- 元の指定頂点自身を頂点とする、元の小さい元の圏上の全密度余錐。 -/
def sigmaVertexDensityCocone :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaElementsYonedaDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafVertexFunctor v)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaDensityCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafVertexFunctor v) (sigmaVertexPresheaf_mem v)

/-- 元の全密度余錐の頂点は元の指定頂点そのもの。 -/
lemma sigmaVertexDensityCocone_vertex : (sigmaVertexDensityCocone v).vertex = v := by
  apply Subtype.ext
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaDensityCocone_vertex _ (sigmaVertexPresheaf_mem v)).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafVertexFunctor_vertex v)

/-- 元の指定頂点への同じ全密度余錐は余極限。 -/
lemma sigmaVertexDensityCocone_isColimit : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (sigmaVertexDensityCocone v) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaDensityCocone_isColimit _ (sigmaVertexPresheaf_mem v)

/-- sifted 保存関手は、元の指定頂点の同じ全密度余錐を余極限へ送る。 -/
lemma sigmaVertexDensity_image_isColimit
    (hC : ∀ (J : Type u) [Finite J] (d : nerve (Discrete J) ⟶ C.op), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit d)
    {D : SSet.{u + 1}} (G : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C ⟶ D)
    (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallSiftedColimits G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone G (sigmaVertexDensityCocone v)) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraightening (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafVertexFunctor v)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafElements_isSifted hC _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafVertexFunctor_preservesFiniteProducts v)
  exact hG _ _ _ (sigmaVertexDensityCocone_isColimit v)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
