module

public import SerrePositivity.InfinityCategories.F2.Presentable.CompactModelGenerators
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulCalculus

/-!
概要：全 compact 小模型の Ind 同値による Yoneda 像を、元の全 compact 圏の新しい小模型として読む。
方針：元の包含との全関手同型で compact 性と本質的全射性を戻す。
規約：新しい模型の元の圏への合成は実際の Ind Yoneda 像そのもの。
使われ方：元の標準 compact comma と Ind 密度余錐の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：全 compact 模型の Ind 同値の実 Yoneda 像も全 compact 圏の小模型となる。
方針：元の模型の像を回収する全関手同型から、全部分制限の全同値を作る。
規約：元の圏への合成の等式を保持する。
使われ方：標準 compact comma の添字を正確な Yoneda 像で比較する。 -/
lemma exists_compactIndYonedaModel {μ : Cardinal.{u}} [Fact μ.IsRegular]
    {A : SSet.{u}} [Quasicategory A] {C : SSet.{u + 1}} [Quasicategory C]
    (a : QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj A)
      (Compact.kappaCompactObjects.{u, u + 1} μ C))
    (e : QCatEquivalence (Ind.IndInfinity μ A) C)
    (β : FunctorIso (Ind.indYoneda μ A ≫ e.hom)
      (a.hom ≫ Compact.kappaCompactInclusion.{u, u + 1} μ C)) :
    ∃ f : QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj A)
      (Compact.kappaCompactObjects.{u, u + 1} μ C),
      f.hom ≫ Compact.kappaCompactInclusion.{u, u + 1} μ C = Ind.indYoneda μ A ≫ e.hom := by
  let j := Compact.kappaCompactInclusion.{u, u + 1} μ C
  let i := Ind.indYoneda μ A ≫ e.hom
  have hi : ∀ v, Compact.IsKappaCompact.{u, u + 1} μ (i.app (Opposite.op ⦋0⦌) v) :=
    fun v ↦ (Compact.isKappaCompact_iff_of_iso (β.app v)).mpr
      (fullSubcomplexOnVertices_vertex (a.hom.app (Opposite.op ⦋0⦌) v))
  let f := fullSubcomplexLift (Compact.IsKappaCompact.{u, u + 1} μ) i hi
  have hf : f ≫ j = i := fullSubcomplexLift_ι _ _ _
  have hj : IsFullyFaithful j := Compact.kappaCompactInclusion_isFullyFaithful μ C
  have hff : IsFullyFaithful f := by
    apply (isFullyFaithful_comp_iff f j hj).mp
    rw [hf]
    exact (Ind.indYoneda_isFullyFaithful μ A).comp e.isQCatEquivalence.isFullyFaithful
  have hes : IsEssentiallySurjective f := by
    intro v
    obtain ⟨w, ⟨ew⟩⟩ := a.isEssentiallySurjective v
    let ev : VertexIso (j.app (Opposite.op ⦋0⦌) (f.app (Opposite.op ⦋0⦌) w))
        (j.app (Opposite.op ⦋0⦌) v) := β.app w ≪≫ VertexIso.map ew j
    exact ⟨w, ⟨hj.preimageVertexIso ev⟩⟩
  exact ⟨qCatEquivalenceOfFullyFaithfulEssentiallySurjective f hff hes, hf⟩

end SerrePositivity.InfinityCategories.F2.Presentable
