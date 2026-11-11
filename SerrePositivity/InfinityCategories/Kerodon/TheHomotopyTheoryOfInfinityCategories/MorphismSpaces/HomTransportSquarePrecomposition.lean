module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerComposition

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomTransportSquareIdentity
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomSpanSectionBoundaryCoherence

/-!
概要：指定輸送正方形の等式を、元の全 Hom 作用で前合成しても同じ四辺を回収する。
方針：同型の前合成の合成則と前後合成の交換を使う。
規約：元の正方形の等式と全境界同型の値を保持する。
使われ方：大域分類 Hom 作用の共有セルの自然性。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 指定正方形は、同じ共通 Hom に写る任意の元の作用で引き戻しても整合する。 -/
lemma HomTransportSquareCommutes.precomp
    {H₀ H₁ X₀ X₁ Y₀ Y₁ K : SSet.{u}}
    (p₀ : H₀ ⟶ X₀) (p₁ : H₀ ⟶ X₁) (q₀ : H₁ ⟶ Y₀) (q₁ : H₁ ⟶ Y₁) (r : H₀ ⟶ H₁)
    (t₀ : X₁ ⟶ X₀) (t₁ : Y₁ ⟶ Y₀) (u₀ : X₀ ⟶ Y₀) (u₁ : X₁ ⟶ Y₁)
    (e₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (p₁ ≫ t₀) p₀) (e₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (q₁ ≫ t₁) q₀)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (p₀ ≫ u₀) (r ≫ q₀))
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (p₁ ≫ u₁) (r ≫ q₁))
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (t₀ ≫ u₀) (u₁ ≫ t₁))
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomTransportSquareCommutes p₀ p₁ q₀ q₁ r t₀ t₁ u₀ u₁ e₀ e₁ h₀ h₁ e)
    (a : K ⟶ H₀) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomTransportSquareCommutes (a ≫ p₀) (a ≫ p₁) q₀ q₁ (a ≫ r)
      t₀ t₁ u₀ u₁ (e₀.precomp a) e₁ (h₀.precomp a) (h₁.precomp a) e := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomTransportSquareCommutes at h ⊢
  have hh := congrArg (fun v ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp v a) h
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_trans, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp,
    ← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp] using hh

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
