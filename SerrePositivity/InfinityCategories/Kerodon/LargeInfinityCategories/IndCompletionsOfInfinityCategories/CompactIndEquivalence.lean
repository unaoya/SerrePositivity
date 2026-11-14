module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndCompactRetraction
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.CompactIndComparisonCriterion
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.RetractReflection

/-!
概要：元の Idem(C) から元の κ-compact Indκ(C) への実比較そのものは全 ∞ 圏同値。
方針：元の任意の compact 頂点の Yoneda retract を同じ全部分圏へ反映し、保存済み判定を使う。
規約：κ は正則。元の比較・両 Yoneda・両包含を保持。本質全射性を入力に仮定しない。
使われ方：F2N-3(d) と F2N-4(e) の比較、および compact Ind の生成。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {C : SSet.{u}} [Quasicategory C]

/-- 元の compact Ind 全部分圏の内部でも、元の全ての頂点は同じ Yoneda 像の retract。 -/
lemma compactInd_retract_yoneda (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (y : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{u, u + 1} κ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) _⦋0⦌) :
    ∃ x : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf y
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.compactIndYoneda κ C).app (Opposite.op ⦋0⦌) (ULift.up x)) := by
  obtain ⟨x, hx⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indCompact_retract_yoneda κ
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion.{u, u + 1} κ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)).app _ y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex y)
  refine ⟨x, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.isVertexRetractOf_iff_map_of_fullyFaithful
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion.{u, u + 1} κ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion_isFullyFaithful κ _) y _).mpr ?_⟩
  have he := congrArg (fun f => f.app (Opposite.op ⦋0⦌) (ULift.up x))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.compactIndYoneda_inclusion (C := C) κ)
  exact he.symm ▸ hx

/-- 元の Idem(C) から compact Indκ(C) への同じ実比較は本質全射。 -/
lemma idemToCompactInd_isEssentiallySurjective (κ : Cardinal.{u}) [Fact κ.IsRegular] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.idemToCompactInd κ C) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.idemToCompactInd_isEssentiallySurjective_iff_retracts κ).mpr (compactInd_retract_yoneda κ)

/-- 正則 κ に対し、元の比較 Idem(C) → Indκ(C)^κ は全 ∞ 圏同値そのもの。 -/
lemma idemToCompactInd_isQCatEquivalence (κ : Cardinal.{u}) [Fact κ.IsRegular] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.idemToCompactInd κ C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.idemToCompactInd_isQCatEquivalence_of_retracts κ (compactInd_retract_yoneda κ)

/-- 同じ元の比較を順方向に持つ、compact Indκ(C) と Idem(C) の実際の同値。 -/
def compactIndEquivalence (κ : Cardinal.{u}) [Fact κ.IsRegular] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Idem C) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{u, u + 1} κ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)) :=
  (idemToCompactInd_isQCatEquivalence (C := C) κ).choose

/-- 同値の順方向は、保存済みの同じ元の比較そのもの。 -/
lemma compactIndEquivalence_hom (κ : Cardinal.{u}) [Fact κ.IsRegular] :
    (compactIndEquivalence (C := C) κ).hom = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.idemToCompactInd κ C := rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BGT "Lemma 2.20" (partial := component) "仮定：小準圏と冪等完備な標的（Lean は安定性を使わない）。結論：完備化への制限による関手圏の同値と、各対象での Idem(C) ≃ Indκ(C)^κ（原典の反射性の各圏での成分と κ=ω の式。Cat^ex 上の大域随伴は含まない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.compactIndEquivalence
