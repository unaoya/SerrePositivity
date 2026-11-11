module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceKanValues
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PointKanExtension
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.GeneratorEquivalence

/-!
概要：増大部分 poset 列の各部分余極限を、一つの列として組み立て和の余極限を回収する。
方針：全空間の段射影に沿う Kan 延長と、和への共終な値射影を組み合わせる。
規約：指定した和の余極限頂点を厳密に保持。使われ方：交互細分の二辺の所属の回収。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceColimits

local instance : Fact Cardinal.aleph0.IsRegular := ⟨Cardinal.isRegular_aleph0⟩
variable {μ : Cardinal.{u}} {J : Type u} [PartialOrder J]

/-- 列の全空間から、元の大きい添字 poset への値射影。 -/
def pieceSequenceTotalOriginalValue (A : ℕ → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceTotal.PieceSequenceTotal A ⥤ J :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceTotal.pieceSequenceTotalValueMonotone A).functor ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.subsetInclusion (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FilteredPieceSequenceUnion.filteredPieceSequenceUnion A)

/-- 指定 fiber と元の値射影の合成は、元の部分集合包含そのもの。 -/
lemma pieceSequenceTotalFiber_originalValue
    (A : ℕ → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceTotal.pieceSequenceTotalFiber A n ⋙ pieceSequenceTotalOriginalValue A =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.subsetInclusion (A n).val := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- 元の全図式を列の全空間へ制限する。 -/
def pieceSequenceTotalDiagram
    (A : ℕ → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J)
    {C : SSet.{u + 1}}
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶ C) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceTotal.PieceSequenceTotal A)) ⟶ C :=
  (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (pieceSequenceTotalOriginalValue A)) ≫ D

/-- 全空間図式の fiber 制限は、元の同じ部分図式と全射で一致する。 -/
lemma pieceSequenceTotalDiagram_restrict_fiber
    (A : ℕ → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J)
    {C : SSet.{u + 1}}
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶ C) (n : ℕ) :
    (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceTotal.pieceSequenceTotalFiber A n)) ≫
      pieceSequenceTotalDiagram A D = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredPartialDiagram D (A n) := by
  have he : nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceTotal.pieceSequenceTotalFiber A n) ≫
      nerveMap (pieceSequenceTotalOriginalValue A) = nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.subsetInclusion (A n).val) := by
    change nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceTotal.pieceSequenceTotalFiber A n ⋙ pieceSequenceTotalOriginalValue A) = _
    rw [pieceSequenceTotalFiber_originalValue]
  dsimp only [pieceSequenceTotalDiagram, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredPartialDiagram]
  rw [← Category.assoc, ← Functor.map_comp, he]

/-- 元の和への制限を、全空間の同じ値射影でさらに制限したものは全空間図式である。 -/
lemma pieceSequenceTotalDiagram_restrict_union
    (A : ℕ → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J)
    {C : SSet.{u + 1}}
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶ C) :
    (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceTotal.pieceSequenceTotalValueMonotone A).functor) ≫
      ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.subsetInclusion (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FilteredPieceSequenceUnion.filteredPieceSequenceUnion A))) ≫ D) =
          pieceSequenceTotalDiagram A D := by
  dsimp only [pieceSequenceTotalDiagram, pieceSequenceTotalOriginalValue]
  change _ = (SSet.uliftFunctor.{u + 1, u}).map
    (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceTotal.pieceSequenceTotalValueMonotone A).functor ≫
      nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.subsetInclusion (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FilteredPieceSequenceUnion.filteredPieceSequenceUnion A))) ≫ D
  rw [Functor.map_comp, Category.assoc]

/-- 各部分余極限を同じ全列の値に取り、その余極限を元の和の指定頂点として回収する。 -/
lemma exists_pieceSequenceColimitPresentation
    (A : ℕ → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J) (hA : Monotone A)
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶ C)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.subsetInclusion (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FilteredPieceSequenceUnion.filteredPieceSequenceUnion A))) ≫ D))
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    ∃ G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶ C,
      (∀ n, ∃ a : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredPartialDiagram D (A n)),
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone a ∧ a.vertex = G.app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULift.up n)))) ∧
      ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone G, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d ∧ d.vertex = c.vertex := by
  let δ := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceTotal.pieceSequenceTotalIndex A))
  let F := pieceSequenceTotalDiagram A D
  obtain ⟨G, β, hβ⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_smallShape_leftKanExtension
    (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceTotal.pieceSequenceTotalIndex A)) hC F
  let q := (SSet.uliftFunctor.{u + 1, u}).map
    (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceTotal.pieceSequenceTotalValueMonotone A).functor)
  have hq := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isRightCofinal_ulift _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceTotal.pieceSequenceTotalValue_nerve_isRightCofinal A hA)
  let e := pieceSequenceTotalDiagram_restrict_union A D
  let a := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq e (c.restrict q)
  have ha : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone a := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_isColimit_iff e _).mp
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isColimitCone_iff_restrict_rightCofinal q hq c).mp hc)
  obtain ⟨d, hd⟩ := hC (nerve (ULift.{u} ℕ)) G
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso d.vertex c.vertex := by
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftKan_colimitVertexIso δ β hβ a ha d hd
    have hv : a.vertex = c.vertex :=
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_vertex e _).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_restrict c q)
    rw [hv] at h
    exact h
  obtain ⟨d', hd', hv'⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_colimitCone_vertex_of_iso d hd hi
  refine ⟨G, ?_, d', hd', hv'⟩
  intro n
  obtain ⟨b, hb, hvb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceKanValues.pieceSequence_leftKan_value_isPartialColimit A hA hβ n
  let he := pieceSequenceTotalDiagram_restrict_fiber A D n
  refine ⟨_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq he b,
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_isColimit_iff he _).mp hb, ?_⟩
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_vertex]
  exact hvb

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceColimits
