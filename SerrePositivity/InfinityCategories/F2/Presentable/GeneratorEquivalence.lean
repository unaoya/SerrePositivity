module

public import SerrePositivity.InfinityCategories.F2.Presentable.CompactEquivalence
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ColimitVertexTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentCoconeTransport
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.CoconeTransformationPointPost

/-!
概要：同じ小さい κ-compact 生成圏と各対象の単一表示を、元の同値で輸送する。
方針：元の全余錐像を保持し、指定された頂点同型を可逆辺として持ち上げる。
規約：新しい余錐の頂点は指定対象に厳密に一致。図式を通常の圏へ置き換えない。
使われ方：κ-accessible 圏の同値不変性と Ind 表現の逆方向。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 指定された頂点同型へ元の全余錐を持ち上げ、指定頂点そのものを得る。 -/
lemma exists_colimitCone_vertex_of_iso {K C : SSet.{u}} [Quasicategory C] {D : K ⟶ C}
    (c : JoinCocone D) (hc : IsColimitCone c) {y : C _⦋0⦌} (e : VertexIso c.vertex y) :
    ∃ d : JoinCocone D, IsColimitCone d ∧ d.vertex = y := by
  obtain ⟨a, ha⟩ := homotopyCategory_homMk_surjective c.vertex y e.hom
  have h : IsInvertibleEdge a := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk a)
    rw [ha]
    infer_instance
  exact exists_colimitCone_vertex_of_invertible c hc (SSet.Edge.ofTruncated a) h

/-- 元の単一 filtered 生成表示を、同じ生成関手の同値像と指定対象へ輸送する。 -/
lemma HasKappaFilteredGeneratorPresentation.of_equivalence {κ : Cardinal.{u}}
    {A : SSet.{u}} {C E : SSet.{u + 1}} [Quasicategory C] [Quasicategory E]
    {i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C} {x : C _⦋0⦌}
    (hx : HasKappaFilteredGeneratorPresentation κ i x) (e : QCatEquivalence C E)
    {y : E _⦋0⦌} (ey : VertexIso (e.hom.app (Opposite.op ⦋0⦌) x) y) :
    HasKappaFilteredGeneratorPresentation κ (i ≫ e.hom) y := by
  obtain ⟨I, hI, hκ, a, c, hv, hc⟩ := hx
  let d := coherentCoconeOfDiagramEq
    (Category.assoc ((SSet.uliftFunctor.{u + 1, u}).map a) i e.hom) (mapJoinCocone e.hom c)
  have hd : IsColimitCone d := (coherentCoconeOfDiagramEq_isColimit_iff _ _).mp
    ((equivalence_isColimitCone_iff e.isQCatEquivalence c).mp hc)
  have hdv : d.vertex = e.hom.app (Opposite.op ⦋0⦌) x := by
    rw [coherentCoconeOfDiagramEq_vertex, Ind.mapJoinCocone_vertex, hv]
  obtain ⟨d', hd', hv'⟩ := exists_colimitCone_vertex_of_iso d hd
    (eqToIso (congrArg HomotopyCategory.mk hdv) ≪≫ ey)
  exact ⟨I, hI, hκ, a, d', hv', hd'⟩

/-- 同じ小さい生成圏の同値像は、同じ濃度で全対象を compact 生成する。 -/
lemma IsKappaCompactGenerating.of_equivalence {κ : Cardinal.{u}}
    {A : SSet.{u}} [Quasicategory A] {C E : SSet.{u + 1}}
    [Quasicategory C] [Quasicategory E] {i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C}
    (hi : IsKappaCompactGenerating κ i) (e : QCatEquivalence C E) :
    IsKappaCompactGenerating κ (i ≫ e.hom) where
  fullyFaithful := hi.fullyFaithful.comp e.isQCatEquivalence.isFullyFaithful
  compact a := isKappaCompact_image_of_equivalence e _ (hi.compact a)
  presentation y := (hi.presentation (e.inv.app (Opposite.op ⦋0⦌) y)).of_equivalence e
    (e.invHomIso.app y)

end SerrePositivity.InfinityCategories.F2.Presentable
