module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.PieceSequenceKanValues
public import SerrePositivity.InfinityCategories.F2.Presentable.PointKanExtension
public import SerrePositivity.InfinityCategories.F2.Presentable.GeneratorEquivalence

/-!
概要：増大部分 poset 列の各部分余極限を、一つの列として組み立て和の余極限を回収する。
方針：全空間の段射影に沿う Kan 延長と、和への共終な値射影を組み合わせる。
規約：指定した和の余極限頂点を厳密に保持。使われ方：交互細分の二辺の所属の回収。
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
variable {μ : Cardinal.{u}} {J : Type u} [PartialOrder J]

/-- 列の全空間から、元の大きい添字 poset への値射影。 -/
def pieceSequenceTotalOriginalValue (A : ℕ → SmallFilteredPieces Cardinal.aleph0 μ J) :
    PieceSequenceTotal A ⥤ J :=
  (pieceSequenceTotalValueMonotone A).functor ⋙ subsetInclusion (filteredPieceSequenceUnion A)

/-- 指定 fiber と元の値射影の合成は、元の部分集合包含そのもの。 -/
lemma pieceSequenceTotalFiber_originalValue
    (A : ℕ → SmallFilteredPieces Cardinal.aleph0 μ J) (n : ℕ) :
    pieceSequenceTotalFiber A n ⋙ pieceSequenceTotalOriginalValue A =
      subsetInclusion (A n).val := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- 元の全図式を列の全空間へ制限する。 -/
def pieceSequenceTotalDiagram
    (A : ℕ → SmallFilteredPieces Cardinal.aleph0 μ J)
    {C : SSet.{u + 1}}
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶ C) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve (PieceSequenceTotal A)) ⟶ C :=
  (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (pieceSequenceTotalOriginalValue A)) ≫ D

/-- 全空間図式の fiber 制限は、元の同じ部分図式と全射で一致する。 -/
lemma pieceSequenceTotalDiagram_restrict_fiber
    (A : ℕ → SmallFilteredPieces Cardinal.aleph0 μ J)
    {C : SSet.{u + 1}}
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶ C) (n : ℕ) :
    (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (pieceSequenceTotalFiber A n)) ≫
      pieceSequenceTotalDiagram A D = smallFilteredPartialDiagram D (A n) := by
  have he : nerveMap (pieceSequenceTotalFiber A n) ≫
      nerveMap (pieceSequenceTotalOriginalValue A) = nerveMap (subsetInclusion (A n).val) := by
    change nerveMap (pieceSequenceTotalFiber A n ⋙ pieceSequenceTotalOriginalValue A) = _
    rw [pieceSequenceTotalFiber_originalValue]
  dsimp only [pieceSequenceTotalDiagram, smallFilteredPartialDiagram]
  rw [← Category.assoc, ← Functor.map_comp, he]

/-- 元の和への制限を、全空間の同じ値射影でさらに制限したものは全空間図式である。 -/
lemma pieceSequenceTotalDiagram_restrict_union
    (A : ℕ → SmallFilteredPieces Cardinal.aleph0 μ J)
    {C : SSet.{u + 1}}
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶ C) :
    (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (pieceSequenceTotalValueMonotone A).functor) ≫
      ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (subsetInclusion (filteredPieceSequenceUnion A))) ≫ D) =
          pieceSequenceTotalDiagram A D := by
  dsimp only [pieceSequenceTotalDiagram, pieceSequenceTotalOriginalValue]
  change _ = (SSet.uliftFunctor.{u + 1, u}).map
    (nerveMap (pieceSequenceTotalValueMonotone A).functor ≫
      nerveMap (subsetInclusion (filteredPieceSequenceUnion A))) ≫ D
  rw [Functor.map_comp, Category.assoc]

/-- 各部分余極限を同じ全列の値に取り、その余極限を元の和の指定頂点として回収する。 -/
lemma exists_pieceSequenceColimitPresentation
    (A : ℕ → SmallFilteredPieces Cardinal.aleph0 μ J) (hA : Monotone A)
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶ C)
    (c : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (subsetInclusion (filteredPieceSequenceUnion A))) ≫ D))
    (hc : IsColimitCone c) :
    ∃ G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶ C,
      (∀ n, ∃ a : JoinCocone (smallFilteredPartialDiagram D (A n)),
        IsColimitCone a ∧ a.vertex = G.app _ (ULift.up (nerveVertex (ULift.up n)))) ∧
      ∃ d : JoinCocone G, IsColimitCone d ∧ d.vertex = c.vertex := by
  let δ := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (pieceSequenceTotalIndex A))
  let F := pieceSequenceTotalDiagram A D
  obtain ⟨G, β, hβ⟩ := exists_smallShape_leftKanExtension
    (nerveMap (pieceSequenceTotalIndex A)) hC F
  let q := (SSet.uliftFunctor.{u + 1, u}).map
    (nerveMap (pieceSequenceTotalValueMonotone A).functor)
  have hq := Ind.isRightCofinal_ulift _ (pieceSequenceTotalValue_nerve_isRightCofinal A hA)
  let e := pieceSequenceTotalDiagram_restrict_union A D
  let a := coherentCoconeOfDiagramEq e (c.restrict q)
  have ha : IsColimitCone a := (coherentCoconeOfDiagramEq_isColimit_iff e _).mp
    ((Ind.isColimitCone_iff_restrict_rightCofinal q hq c).mp hc)
  obtain ⟨d, hd⟩ := hC (nerve (ULift.{u} ℕ)) G
  have hi : VertexIso d.vertex c.vertex := by
    have h := leftKan_colimitVertexIso δ β hβ a ha d hd
    have hv : a.vertex = c.vertex :=
      (coherentCoconeOfDiagramEq_vertex e _).trans (JoinCocone.vertex_restrict c q)
    rw [hv] at h
    exact h
  obtain ⟨d', hd', hv'⟩ := exists_colimitCone_vertex_of_iso d hd hi
  refine ⟨G, ?_, d', hd', hv'⟩
  intro n
  obtain ⟨b, hb, hvb⟩ := pieceSequence_leftKan_value_isPartialColimit A hA hβ n
  let he := pieceSequenceTotalDiagram_restrict_fiber A D n
  refine ⟨coherentCoconeOfDiagramEq he b,
    (coherentCoconeOfDiagramEq_isColimit_iff he _).mp hb, ?_⟩
  rw [coherentCoconeOfDiagramEq_vertex]
  exact hvb

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
