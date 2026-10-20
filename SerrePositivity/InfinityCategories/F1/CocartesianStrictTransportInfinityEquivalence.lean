module

public import SerrePositivity.InfinityCategories.F1.CocartesianStrictTransportEnriched
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulEquivalence

/-!
概要：元の cocartesian fibration の ∞ 圏と strict transport の像の ∞ 圏との同値。
方針：同じ coherent 比較の充満忠実性と、図式の表示による本質的全射性を合わせる。
規約：全ての Cat∞ 値 coherent 図式を対象とする分類同値はまだ主張しない。
使われ方：同じ strict transport の実現を経由する分類主写像の Hom 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 中間の比較は、元の fibration をその同じ strict transport の標準頂点へ送る。 -/
lemma cocartesianStrictTransportInfinityMap_vertex {C : Type u} [Category.{u} C]
    (p : CocartesianFibrationCategory (nerve C)) :
    (cocartesianStrictTransportInfinityMap C).app (Opposite.op ⦋0⦌) (coherentNerveVertex p) =
      coherentNerveVertex
        (show CocartesianTransportDiagramCategory C from cocartesianTransportDiagramImage p) :=
  coherentNerveMap_vertex (cocartesianStrictTransportCoreEnriched (C := C)) p

/-- strict transport の像への同じ比較は、図式の表示から本質的全射。 -/
lemma cocartesianStrictTransportInfinityMap_isEssentiallySurjective
    (C : Type u) [Category.{u} C] :
    IsEssentiallySurjective (cocartesianStrictTransportInfinityMap C) := by
  intro y
  let F : CocartesianTransportDiagramCategory C := coherentNerveObject y
  obtain ⟨p, hp⟩ := F.property
  refine ⟨coherentNerveVertex (show CocartesianFibrationCategory (nerve C) from p), ?_⟩
  rw [cocartesianStrictTransportInfinityMap_vertex]
  have h : (show CocartesianTransportDiagramCategory C from cocartesianTransportDiagramImage p) =
      F := Subtype.ext hp
  exact ⟨eqToIso (congrArg SSet.HomotopyCategory.mk
    ((congrArg coherentNerveVertex h).trans (coherentNerveVertex_object y)))⟩

/-- 元の全相対 Hom の core を保ったまま、strict transport の像への同値を得る。 -/
lemma cocartesianStrictTransportInfinityMap_isQCatEquivalence
    (C : Type u) [Category.{u} C] : IsQCatEquivalence (cocartesianStrictTransportInfinityMap C) :=
  isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (cocartesianStrictTransportInfinityMap_isFullyFaithful C)
    (cocartesianStrictTransportInfinityMap_isEssentiallySurjective C)

/-- 順方向を同じ元の coherent 比較に固定した中間の同値データ。 -/
def cocartesianStrictTransportInfinityEquivalence (C : Type u) [Category.{u} C] :
    QCatEquivalence (CocartesianFibrationInfinity (nerve C))
      (CocartesianTransportDiagramInfinity C) :=
  (cocartesianStrictTransportInfinityMap_isQCatEquivalence C).choose

end SerrePositivity.InfinityCategories
