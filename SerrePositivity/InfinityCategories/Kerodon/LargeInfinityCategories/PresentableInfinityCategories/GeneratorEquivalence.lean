module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompactEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitVertexTransport
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentCoconeTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoconeTransformationPointPost

/-!
概要：同じ小さい κ-compact 生成圏と各対象の単一表示を、元の同値で輸送する。
方針：元の全余錐像を保持し、指定された頂点同型を可逆辺として持ち上げる。
規約：新しい余錐の頂点は指定対象に厳密に一致。図式を通常の圏へ置き換えない。
使われ方：κ-accessible 圏の同値不変性と Ind 表現の逆方向。

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


/-- 指定された頂点同型へ元の全余錐を持ち上げ、指定頂点そのものを得る。 -/
lemma exists_colimitCone_vertex_of_iso {K C : SSet.{u}} [Quasicategory C] {D : K ⟶ C}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) {y : C _⦋0⦌} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso c.vertex y) :
    ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d ∧ d.vertex = y := by
  obtain ⟨a, ha⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective c.vertex y e.hom
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge a := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk a)
    rw [ha]
    infer_instance
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_colimitCone_vertex_of_invertible c hc (SSet.Edge.ofTruncated a) h

/-- 元の単一 filtered 生成表示を、同じ生成関手の同値像と指定対象へ輸送する。 -/
lemma HasKappaFilteredGeneratorPresentation.of_equivalence {κ : Cardinal.{u}}
    {A : SSet.{u}} {C E : SSet.{u + 1}} [Quasicategory C] [Quasicategory E]
    {i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C} {x : C _⦋0⦌}
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.HasKappaFilteredGeneratorPresentation κ i x) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence C E)
    {y : E _⦋0⦌} (ey : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (e.hom.app (Opposite.op ⦋0⦌) x) y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.HasKappaFilteredGeneratorPresentation κ (i ≫ e.hom) y := by
  obtain ⟨I, hI, hκ, a, c, hv, hc⟩ := hx
  let d := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq
    (Category.assoc ((SSet.uliftFunctor.{u + 1, u}).map a) i e.hom) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone e.hom c)
  have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_isColimit_iff _ _).mp
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.equivalence_isColimitCone_iff e.isQCatEquivalence c).mp hc)
  have hdv : d.vertex = e.hom.app (Opposite.op ⦋0⦌) x := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.mapJoinCocone_vertex, hv]
  obtain ⟨d', hd', hv'⟩ := exists_colimitCone_vertex_of_iso d hd
    (eqToIso (congrArg HomotopyCategory.mk hdv) ≪≫ ey)
  exact ⟨I, hI, hκ, a, d', hv', hd'⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.HasKappaFilteredGeneratorPresentation export _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HasKappaFilteredGeneratorPresentation (of_equivalence)


/-- 同じ小さい生成圏の同値像は、同じ濃度で全対象を compact 生成する。 -/
lemma IsKappaCompactGenerating.of_equivalence {κ : Cardinal.{u}}
    {A : SSet.{u}} [Quasicategory A] {C E : SSet.{u + 1}}
    [Quasicategory C] [Quasicategory E] {i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C}
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaCompactGenerating κ i) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence C E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaCompactGenerating κ (i ≫ e.hom) where
  fullyFaithful := hi.fullyFaithful.comp e.isQCatEquivalence.isFullyFaithful
  compact a := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isKappaCompact_image_of_equivalence e _ (hi.compact a)
  presentation y := (hi.presentation (e.inv.app (Opposite.op ⦋0⦌) y)).of_equivalence e
    (e.invHomIso.app y)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaCompactGenerating export _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaCompactGenerating (of_equivalence)


end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
