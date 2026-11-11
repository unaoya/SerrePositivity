module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompactEndpoints
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompactArrows
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorPresentable

/-!
概要：元の射圏と元の圏が共に accessible となり、生成射と両端点が compact となる濃度。
方針：公開済みの関手圏 presentable 性と共通 compact 濃度を、正当な濃度変更で揃える。
規約：濃度の単なる大小から accessibility を主張しない。
使われ方：P-1 f2、HTT 5.5.4.14 の生成元を含む compact な小模型。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 元の各辺を射圏の実頂点として読む。 -/
def generatorArrowVertex (edges : I → C _⦋1⦌) (i : I) :
    ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.yonedaEquiv.symm (edges i))

omit [Quasicategory C] in
/-- 頂点として読んだ生成辺は、元の指定一次単体そのもの。 -/
lemma generatorArrowVertex_edge (edges : I → C _⦋1⦌) (i : I) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge (generatorArrowVertex edges i) = edges i := by
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[1] C).symm
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[1] C) (SSet.yonedaEquiv.symm (edges i)))) = edges i
  rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- 小さい一点単体の宇宙変更を戻すと、元の全射圏も presentable。 -/
lemma arrow_isPresentable (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable ((ihom (Δ[1] : SSet.{u + 1})).obj C) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functor_isPresentable (Δ[1] : SSet.{u}) hC).of_equivalence
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, u + 1} 1)).precompose C).symm

/-- 両方の accessibility と生成射・両端点の compact 性を一つの正則濃度で実証する。 -/
lemma exists_regular_generatorArrowCardinal (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C)
    (edges : I → C _⦋1⦌) (σ : Cardinal.{u}) :
    ∃ μ : Cardinal.{u}, μ.IsRegular ∧ σ < μ ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ C ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ ((ihom (Δ[1] : SSet.{u + 1})).obj C) ∧
      (∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (generatorArrowVertex edges i)) ∧
      ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (C.δ 1 (edges i)) ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (C.δ 0 (edges i)) := by
  have hA := arrow_isPresentable hC
  obtain ⟨κC, hκC⟩ := hC.isAccessible
  obtain ⟨κA, hκA⟩ := hA.isAccessible
  obtain ⟨ρA, _, _, hgen⟩ :=
    hA.isAccessible.exists_common_compactCardinal (generatorArrowVertex edges) σ
  obtain ⟨ρC, _, _, hend⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_regular_compactEndpoints hC edges σ
  let κ : ULift.{u} Bool → Cardinal.{u} := fun b ↦ if b.down then κC else κA
  obtain ⟨μ, hμ, hbound, hb⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_regular_cardinalChangeBound_family κ (max σ (max ρA ρC))
  have : Fact μ.IsRegular := ⟨hμ⟩
  have hσ : σ < μ := lt_of_le_of_lt (le_max_left _ _) hbound
  have hρA : ρA ≤ μ := ((le_max_left ρA ρC).trans (le_max_right σ _)).trans hbound.le
  have hρC : ρC ≤ μ := ((le_max_right ρA ρC).trans (le_max_right σ _)).trans hbound.le
  exact ⟨μ, hμ, hσ, hκC.of_cardinalChangeBound (hb ⟨true⟩),
    hκA.of_cardinalChangeBound (hb ⟨false⟩), fun i ↦ (hgen i).of_le hρA,
    fun i ↦ ⟨((hend i).1).of_le hρC, ((hend i).2).of_le hρC⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
