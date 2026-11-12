module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFamilySquare
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SlicePrismSquare

/-!
概要：二重 prism をパラメータ関手圏の実正方形へ移す。
方針：二時間とパラメータを並べ替えて curry する。
規約：全境界を厳密に保持する。使われ方：屋根合成の族の比較。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries
/-- 全パラメータを内部 Hom の始域へ移し、二つの時間を正方形に保持する。 -/
noncomputable def prismFunctorSquare {K X : SSet.{u}}
    (T : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ K) ⟶ X) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom K).obj X :=
  curry ((β_ K ((Δ[1] : SSet.{u}) ⊗ Δ[1])).hom ≫ (α_ Δ[1] Δ[1] K).hom ≫ T)
/-- 内側の時間の両端は、元の二重 prism の同じ制限の curry。 -/
lemma prismFunctorSquare_inner {K X : SSet.{u}}
    (T : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ K) ⟶ X) (i : Fin 2) :
    (if i = 0 then SSet.ι₀ else SSet.ι₁) ≫ prismFunctorSquare T =
      curry ((β_ K (Δ[1] : SSet.{u})).hom ≫
        (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i K) ≫ T) := by
  apply uncurry_injective
  rw [uncurry_natural_left]
  simp only [prismFunctorSquare, uncurry_curry]
  have hc : K ◁ (if i = 0 then SSet.ι₀ else SSet.ι₁) ≫
      (β_ K ((Δ[1] : SSet.{u}) ⊗ Δ[1])).hom ≫ (α_ Δ[1] Δ[1] K).hom =
        (β_ K (Δ[1] : SSet.{u})).hom ≫ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i K) := by
    fin_cases i <;> apply SSet.hom_ext <;> intro n <;>
      apply ConcreteCategory.hom_ext <;> intro s <;> rfl
  simpa only [Category.assoc] using congrArg (fun k => k ≫ T) hc
/-- 外側の時間の両端も、元の二重 prism の同じ制限の curry。 -/
lemma prismFunctorSquare_outer {K X : SSet.{u}}
    (T : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ K) ⟶ X) (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i (Δ[1] : SSet.{u}) ≫ prismFunctorSquare T =
      curry ((β_ K (Δ[1] : SSet.{u})).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i (Δ[1] ⊗ K) ≫ T) := by
  apply uncurry_injective
  rw [uncurry_natural_left]
  simp only [prismFunctorSquare, uncurry_curry]
  have hc : K ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i (Δ[1] : SSet.{u}) ≫
      (β_ K ((Δ[1] : SSet.{u}) ⊗ Δ[1])).hom ≫ (α_ Δ[1] Δ[1] K).hom =
        (β_ K (Δ[1] : SSet.{u})).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i (Δ[1] ⊗ K) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    rfl
  simpa only [Category.assoc] using congrArg (fun k => k ≫ T) hc
end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries
