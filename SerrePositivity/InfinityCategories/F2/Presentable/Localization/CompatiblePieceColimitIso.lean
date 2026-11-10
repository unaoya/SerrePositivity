module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CompatiblePiecePresentations

/-!
概要：比較対の実余錐から、任意の指定部分余極限の頂点同型を回収する。
方針：対象上の元の余極限を射影し、指定余錐との一意的な余極限比較を合成する。
規約：各頂点の同型を coherent な自然同型とは扱わない。使われ方：同時細分の段の所属判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
local instance : Fact Cardinal.aleph0.IsRegular := ⟨Cardinal.isRegular_aleph0⟩

/-- 元の比較対の両部分余極限は、任意の指定余極限余錐の頂点としても同型。 -/
lemma nonempty_compatiblePiece_colimitVertexIso
    {μ : Cardinal.{u}} {C : SSet.{u + 1}} [Quasicategory C]
    {A₀ A₁ : Type u} [PartialOrder A₀] [PartialOrder A₁]
    {D₀ : (SSet.uliftFunctor.{u + 1, u}).obj (nerve A₀) ⟶ C}
    {D₁ : (SSet.uliftFunctor.{u + 1, u}).obj (nerve A₁) ⟶ C}
    {c₀ : JoinCocone D₀} {c₁ : JoinCocone D₁} {hv : c₀.vertex = c₁.vertex}
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (P : CompatiblePresentationPieces μ c₀ c₁ hv)
    (a₀ : JoinCocone (smallFilteredPartialDiagram D₀ (compatibleLeftPiece P)))
    (ha₀ : IsColimitCone a₀)
    (a₁ : JoinCocone (smallFilteredPartialDiagram D₁ (compatibleRightPiece P)))
    (ha₁ : IsColimitCone a₁) : Nonempty (VertexIso a₀.vertex a₁.vertex) := by
  obtain ⟨b₀, b₁, hb₀, hb₁, ⟨e⟩⟩ := P.property.2.2.2.2
  let π := sliceOverProjection (SSet.yonedaEquiv.symm c₀.vertex)
  have he₀ : ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (subsetInclusion P.val.1)) ≫
      coconeSliceDiagram c₀) ≫ π = smallFilteredPartialDiagram D₀ (compatibleLeftPiece P) := by
    dsimp only [π]
    rw [Category.assoc, coconeSliceDiagram_projection]
    rfl
  have he₁ : ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (subsetInclusion P.val.2)) ≫
      transportedCoconeSliceDiagram c₁ c₀.vertex hv.symm) ≫ π =
        smallFilteredPartialDiagram D₁ (compatibleRightPiece P) := by
    dsimp only [π]
    rw [Category.assoc, transportedCoconeSliceDiagram_projection]
    rfl
  let d₀ := coherentCoconeOfDiagramEq he₀ (mapJoinCocone π b₀)
  let d₁ := coherentCoconeOfDiagramEq he₁ (mapJoinCocone π b₁)
  have hd₀ : IsColimitCone d₀ :=
    (coherentCoconeOfDiagramEq_isColimit_iff he₀ _).mp
      (sliceOverProjection_preservesSmallColimits hC _ _ _ b₀ hb₀)
  have hd₁ : IsColimitCone d₁ :=
    (coherentCoconeOfDiagramEq_isColimit_iff he₁ _).mp
      (sliceOverProjection_preservesSmallColimits hC _ _ _ b₁ hb₁)
  have h₀ : d₀.vertex = π.app _ b₀.vertex :=
    (coherentCoconeOfDiagramEq_vertex he₀ _).trans (Ind.mapJoinCocone_vertex π b₀)
  have h₁ : d₁.vertex = π.app _ b₁.vertex :=
    (coherentCoconeOfDiagramEq_vertex he₁ _).trans (Ind.mapJoinCocone_vertex π b₁)
  have ed : VertexIso d₀.vertex d₁.vertex := by
    rw [h₀, h₁]
    exact e.map π
  exact ⟨colimitVertexIso a₀ d₀ ha₀ hd₀ ≪≫ ed ≪≫ colimitVertexIso d₁ a₁ hd₁ ha₁⟩

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
