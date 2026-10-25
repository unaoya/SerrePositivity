module

public import SerrePositivity.InfinityCategories.F2.Presentable.SmallCompactModels
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessibleIndRepresentation
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanDiagramColimitTransport

/-!
概要：全 compact 対象の任意の小さい全同値模型は、同じ濃度の compact 生成圏となる。
方針：元の生成表示を全部分圏へ持ち上げ、模型同値の逆で全図式を戻す。
規約：各対象の指定頂点と全余錐を保持する。
使われ方：compact 始域 comma の標準余錐の密度比較。
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

/-- 概要：全 μ-compact 全部分圏の小模型の包含は μ-compact 生成関手となる。
方針：元の各 filtered 表示を同値の逆で小模型へ移し、全関手同型で余極限を戻す。
規約：元の圏の固定頂点写像の厳密な小ささは不要。
使われ方：全 compact 模型からの Ind 比較と標準密度余錐。 -/
lemma IsKappaAccessible.compactModel_isKappaCompactGenerating
    {μ : Cardinal.{u}} {C : SSet.{u + 1}} [Quasicategory C]
    (hC : IsKappaAccessible μ C) {A : SSet.{u}} [Quasicategory A]
    (e : QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj A)
      (Compact.kappaCompactObjects.{u, u + 1} μ C)) :
    IsKappaCompactGenerating μ (e.hom ≫ Compact.kappaCompactInclusion.{u, u + 1} μ C) := by
  let j := Compact.kappaCompactInclusion.{u, u + 1} μ C
  refine ⟨e.isQCatEquivalence.isFullyFaithful.comp
    (Compact.kappaCompactInclusion_isFullyFaithful μ C), ?_, ?_⟩
  · intro a
    exact fullSubcomplexOnVertices_vertex (e.hom.app (Opposite.op ⦋0⦌) (ULift.up a))
  · intro x
    obtain ⟨B, hB, i, hi⟩ := hC.2.2
    have := hB
    obtain ⟨I, hI, hfiltered, d, c, hv, hc⟩ := hi.presentation x
    have := hI
    have := hfiltered
    let D := (SSet.uliftFunctor.{u + 1, u}).map d ≫ i
    let H := fullSubcomplexLift (Compact.IsKappaCompact.{u, u + 1} μ) D (by
      rintro ⟨k⟩
      exact hi.compact (d.app (Opposite.op ⦋0⦌) k))
    let a := uliftMorphismDown (H ≫ e.inv)
    have ha : (SSet.uliftFunctor.{u + 1, u}).map a = H ≫ e.inv := uliftMorphismDown_lift _
    have he : FunctorIso ((SSet.uliftFunctor.{u + 1, u}).map a ≫ (e.hom ≫ j)) D := by
      rw [ha, Category.assoc]
      simpa only [Category.assoc, Category.id_comp, H, j, Compact.kappaCompactInclusion,
        fullSubcomplexLift_ι] using (e.invHomIso.precomp H).postcomp j
    obtain ⟨c', hc', hv'⟩ := exists_colimitCocone_functorIso_sameVertex he.symm c hc
    exact ⟨I, hI, hfiltered, a, c', hv'.trans hv, hc'⟩

/-- 概要：指定した全 compact 小模型から、元の圏への全 Ind 同値を構成する。
方針：同じ模型の生成性を実証済み Ind 比較の同値判定へ渡す。
規約：全 compact 模型と元の包含を全関手同型で回収する。
使われ方：標準 compact comma の全密度余錐の構成。 -/
lemma IsKappaAccessible.exists_compactModelIndRepresentation
    {μ : Cardinal.{u}} {C : SSet.{u + 1}} [Quasicategory C]
    (hC : IsKappaAccessible μ C) {A : SSet.{u}} [Quasicategory A]
    (e : QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj A)
      (Compact.kappaCompactObjects.{u, u + 1} μ C)) :
    ∃ g : QCatEquivalence (Ind.IndInfinity μ A) C,
      IsKappaAccessibleFunctor μ g.hom ∧ Nonempty (FunctorIso (Ind.indYoneda μ A ≫ g.hom)
        (e.hom ≫ Compact.kappaCompactInclusion.{u, u + 1} μ C)) := by
  have : Fact μ.IsRegular := ⟨hC.1⟩
  have hi := hC.compactModel_isKappaCompactGenerating e
  obtain ⟨G, hG, ⟨β⟩⟩ := Presentable.exists_indComparison hC.2.1
    (e.hom ≫ Compact.kappaCompactInclusion.{u, u + 1} μ C)
  exact ⟨indComparisonEquivalence hi hG β, hG, ⟨β⟩⟩

end SerrePositivity.InfinityCategories.F2.Presentable
