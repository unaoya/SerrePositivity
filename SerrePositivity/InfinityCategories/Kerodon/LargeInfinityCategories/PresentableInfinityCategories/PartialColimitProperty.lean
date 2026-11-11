module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceColimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CommonRefinementConditions

/-!
概要：小余極限と同型で閉じた頂点条件は、増大部分表示の和の余極限へ移る。
方針：元の実部分余極限を Kan 延長値へ移し、その列の指定余極限へ閉性を適用する。
規約：単なる頂点ごとの比較を自然同型とみなさない。使われ方：二辺の所属条件の可算和閉性。

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

local instance : Fact Cardinal.aleph0.IsRegular := ⟨Cardinal.isRegular_aleph0⟩
variable {μ : Cardinal.{u}} {J : Type u} [PartialOrder J]
  {C : SSet.{u + 1}} [Quasicategory C]

/-- 元の小部分図式の実余極限頂点が、指定した条件に属すこと。 -/
def HasPropertyPartialColimit (W : C _⦋0⦌ → Prop)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶ C)
    (A : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J) : Prop :=
  ∃ a : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredPartialDiagram D A), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone a ∧ W a.vertex

/-- 各段の実部分余極限が条件に属すなら、和の指定余極限頂点も同じ条件に属す。 -/
lemma property_pieceSequenceUnion_colimit
    (W : C _⦋0⦌ → Prop) (hiso : ∀ {x y}, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y → (W x ↔ W y))
    (hclosed : ∀ (K : SSet.{u}) (E : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C),
      (∀ k, W (E.app _ k)) → ∀ a : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone E, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone a → W a.vertex)
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶ C)
    (A : ℕ → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J) (hA : Monotone A)
    (hW : ∀ n, HasPropertyPartialColimit W D (A n))
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.subsetInclusion (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FilteredPieceSequenceUnion.filteredPieceSequenceUnion A))) ≫ D))
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) : W c.vertex := by
  obtain ⟨G, hG, d, hd, hv⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PieceSequenceColimits.exists_pieceSequenceColimitPresentation A hA hC D c hc
  have hWG : ∀ k, W (G.app (Opposite.op ⦋0⦌) k) := by
    rintro ⟨k⟩
    obtain ⟨i, rfl⟩ := nerveEquiv.symm.surjective k
    rcases i with ⟨n⟩
    obtain ⟨a, ha, hWa⟩ := hW n
    obtain ⟨b, hb, hvb⟩ := hG n
    have hWb := (hiso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitVertexIso a b ha hb)).mp hWa
    rwa [hvb] at hWb
  have hm := hclosed _ G hWG d hd
  rwa [hv] at hm

/-- 部分余極限の所属条件は、増大する小さい filtered 部分集合列の和で閉じる。 -/
lemma hasPropertyPartialColimit_sequenceUnion [Fact μ.IsRegular]
    (hμ : Cardinal.aleph0 < μ)
    (W : C _⦋0⦌ → Prop) (hiso : ∀ {x y}, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y → (W x ↔ W y))
    (hclosed : ∀ (K : SSet.{u}) (E : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C),
      (∀ k, W (E.app _ k)) → ∀ a : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone E, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone a → W a.vertex)
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶ C)
    (A : ℕ → _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces Cardinal.aleph0 μ J) (hA : Monotone A)
    (hW : ∀ n, HasPropertyPartialColimit W D (A n)) :
    HasPropertyPartialColimit W D (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CommonRefinementConditions.filteredPieceSequenceUnionPiece hμ A hA) := by
  obtain ⟨c, hc⟩ := hC _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredPartialDiagram D (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CommonRefinementConditions.filteredPieceSequenceUnionPiece hμ A hA))
  exact ⟨c, hc, property_pieceSequenceUnion_colimit W hiso hclosed hC D A hA hW c hc⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
