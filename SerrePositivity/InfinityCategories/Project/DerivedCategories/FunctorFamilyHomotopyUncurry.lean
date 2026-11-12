module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SpanHomotopyGluing
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy
/-!
概要：関手空間への族ホモトピーを、二重パラメータ全体の実ホモトピーへ展開する。
方針：全円柱を uncurry し、結合子で時間を最後に保つ。
規約：全時刻と二つのパラメータを保持する。使われ方：全降下選択空間上の合成関係。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
/-- 関手空間への実ホモトピーを、二重パラメータ全体の実ホモトピーへ戻す。 -/
def functorFamilyHomotopyUncurry {K S Z : SSet.{u}} {f g : S ⟶ (ihom K).obj Z}
    (H : SSet.Homotopy f g) : SSet.Homotopy (uncurry f) (uncurry g) where
  h := (α_ K S (Δ[1] : SSet.{u})).hom ≫ uncurry H.h
  h₀ := by
    change SSet.ι₀ ≫ ((α_ K S (Δ[1] : SSet.{u})).hom ≫ uncurry H.h) = uncurry f
    have h : (SSet.ι₀ : K ⊗ S ⟶ _) ≫ (α_ K S (Δ[1] : SSet.{u})).hom =
        K ◁ (SSet.ι₀ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) := rfl
    rw [← Category.assoc, h, ← uncurry_natural_left, H.h₀]
  h₁ := by
    change SSet.ι₁ ≫ ((α_ K S (Δ[1] : SSet.{u})).hom ≫ uncurry H.h) = uncurry g
    have h : (SSet.ι₁ : K ⊗ S ⟶ _) ≫ (α_ K S (Δ[1] : SSet.{u})).hom =
        K ◁ (SSet.ι₁ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) := rfl
    rw [← Category.assoc, h, ← uncurry_natural_left, H.h₁]
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property
/-- 関手空間への族の同型も、全パラメータ上の一つの実ホモトピーを供給する。 -/
def functorFamilyIsoUncurry {K S Z : SSet.{u}} [Quasicategory Z]
    {f g : S ⟶ (ihom K).obj Z} (I : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) :
    SSet.Homotopy (uncurry f) (uncurry g) :=
  functorFamilyHomotopyUncurry I.simplicialHomotopy
/-- 一つの評価族への全選択空間上の同型を、任意の選択パラメータ全体で展開する。 -/
def functorFamilyIsoUncurry_const {K S T Z : SSet.{u}} [Quasicategory Z]
    {f : S ⟶ (ihom K).obj Z} (g : K ⟶ Z)
    (I : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g))) (p : T ⟶ S) :
    SSet.Homotopy (uncurry (p ≫ f)) (CartesianMonoidalCategory.fst K T ≫ g) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget (functorFamilyIsoUncurry (I.precomp p)) rfl (by
    rw [SSet.comp_const, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex])
end SerrePositivity.InfinityCategories.Project.DerivedCategories
