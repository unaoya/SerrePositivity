module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessibleFunctor
public import SerrePositivity.InfinityCategories.F2.Ind.IndRestrictionEquivalence

/-!
概要：κ-accessible 圏の小さい生成圏から、Indκ 上の保存的延長を構成する。
方針：F1 の同じ Yoneda に沿う左 Kan 延長と指定単位の回収比較を再利用する。
規約：比較の同値性はここでは結論しない。生成関手を全自然同型で回収する。
使われ方：HTT 5.4.2、compact 生成から Ind 表現への比較関手。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 小さい生成圏の元の関手を回収する、κ-filtered 余極限を保つ Ind 上の延長。 -/
lemma exists_indComparison {κ : Cardinal.{u}} [Fact κ.IsRegular]
    {A : SSet.{u}} [Quasicategory A] {C : SSet.{u + 1}} [Quasicategory C]
    (hC : Ind.HasSmallKappaFilteredColimits κ C)
    (i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C) :
    ∃ G : Ind.IndInfinity κ A ⟶ C,
      IsKappaAccessibleFunctor κ G ∧ Nonempty (FunctorIso (Ind.indYoneda κ A ≫ G) i) := by
  obtain ⟨G, β, hβ⟩ := Ind.ind_exists_leftKanExtension κ hC i
  exact ⟨G, Ind.indLeftKanExtension_preservesSmallKappaFilteredColimits κ β hβ,
    ⟨Ind.indLeftKanExtensionRecoveryIso κ β hβ⟩⟩

/-- accessibility の定義の実際の小さい生成圏と、それからの同じ Ind 比較を得る。 -/
lemma IsKappaAccessible.exists_indComparison {κ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] (h : IsKappaAccessible κ C) :
    ∃ (A : SSet.{u}) (hA : Quasicategory A),
      letI := hA
      ∃ (i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C) (G : Ind.IndInfinity κ A ⟶ C),
        IsKappaCompactGenerating κ i ∧ IsKappaAccessibleFunctor κ G ∧
          Nonempty (FunctorIso (Ind.indYoneda κ A ≫ G) i) := by
  obtain ⟨hκ, hC, A, hA, i, hi⟩ := h
  have := hA
  have : Fact κ.IsRegular := ⟨hκ⟩
  obtain ⟨G, hG, e⟩ := Presentable.exists_indComparison hC i
  exact ⟨A, hA, i, G, hi, hG, e⟩

end SerrePositivity.InfinityCategories.F2.Presentable
