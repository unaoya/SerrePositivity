module

public import SerrePositivity.InfinityCategories.F2.Compact.IndCompactRetraction
public import SerrePositivity.InfinityCategories.F2.Compact.CompactIndComparisonCriterion
public import SerrePositivity.InfinityCategories.Core.Idempotent.RetractReflection

/-!
概要：元の Idem(C) から元の κ-compact Indκ(C) への実比較そのものは全 ∞ 圏同値。
方針：元の任意の compact 頂点の Yoneda retract を同じ全部分圏へ反映し、保存済み判定を使う。
規約：κ は正則。元の比較・両 Yoneda・両包含を保持。本質全射性を入力に仮定しない。
使われ方：F2N-3(d) と F2N-4(e) の比較、および compact Ind の生成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
variable {C : SSet.{u}} [Quasicategory C]

/-- 元の compact Ind 全部分圏の内部でも、元の全ての頂点は同じ Yoneda 像の retract。 -/
lemma compactInd_retract_yoneda (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (y : kappaCompactObjects.{u, u + 1} κ (Ind.IndInfinity κ C) _⦋0⦌) :
    ∃ x : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf y
      ((compactIndYoneda κ C).app (Opposite.op ⦋0⦌) (ULift.up x)) := by
  obtain ⟨x, hx⟩ := indCompact_retract_yoneda κ
    ((kappaCompactInclusion.{u, u + 1} κ (Ind.IndInfinity κ C)).app _ y)
    (fullSubcomplexOnVertices_vertex y)
  refine ⟨x, (Idempotent.isVertexRetractOf_iff_map_of_fullyFaithful
    (kappaCompactInclusion.{u, u + 1} κ (Ind.IndInfinity κ C))
    (kappaCompactInclusion_isFullyFaithful κ _) y _).mpr ?_⟩
  have he := congrArg (fun f => f.app (Opposite.op ⦋0⦌) (ULift.up x))
    (compactIndYoneda_inclusion (C := C) κ)
  exact he.symm ▸ hx

/-- 元の Idem(C) から compact Indκ(C) への同じ実比較は本質全射。 -/
lemma idemToCompactInd_isEssentiallySurjective (κ : Cardinal.{u}) [Fact κ.IsRegular] :
    IsEssentiallySurjective (idemToCompactInd κ C) :=
  (idemToCompactInd_isEssentiallySurjective_iff_retracts κ).mpr (compactInd_retract_yoneda κ)

/-- 正則 κ に対し、元の比較 Idem(C) → Indκ(C)^κ は全 ∞ 圏同値そのもの。 -/
lemma idemToCompactInd_isQCatEquivalence (κ : Cardinal.{u}) [Fact κ.IsRegular] :
    IsQCatEquivalence (idemToCompactInd κ C) :=
  idemToCompactInd_isQCatEquivalence_of_retracts κ (compactInd_retract_yoneda κ)

/-- 同じ元の比較を順方向に持つ、compact Indκ(C) と Idem(C) の実際の同値。 -/
def compactIndEquivalence (κ : Cardinal.{u}) [Fact κ.IsRegular] :
    QCatEquivalence (Idempotent.Idem C) (kappaCompactObjects.{u, u + 1} κ (Ind.IndInfinity κ C)) :=
  (idemToCompactInd_isQCatEquivalence (C := C) κ).choose

/-- 同値の順方向は、保存済みの同じ元の比較そのもの。 -/
lemma compactIndEquivalence_hom (κ : Cardinal.{u}) [Fact κ.IsRegular] :
    (compactIndEquivalence (C := C) κ).hom = idemToCompactInd κ C := rfl

end SerrePositivity.InfinityCategories.F2.Compact
