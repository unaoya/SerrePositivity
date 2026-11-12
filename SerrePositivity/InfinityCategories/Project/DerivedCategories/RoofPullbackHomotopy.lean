module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RoofPullbackEdge
/-!
概要：全時刻で同じ底を持つ二つの実ホモトピーを pullback 内で組にする。
方針：円柱の写像を pullback に持ち上げ、両端を二射影で照合する。
規約：充填性・有限性を仮定しない。使われ方：任意標的の実屋根の族比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits MonoidalCategory SSet
open scoped _root_.Simplicial
/-- 同じ底の二つの実ホモトピーを、同じ指定両端を持つ pullback の実ホモトピーにする。 -/
def roofPullbackHomotopy {K A B C : SSet.{u}} (f : A ⟶ C) (g : B ⟶ C)
    {a b : K ⟶ pullback f g}
    (h₁ : SSet.Homotopy (a ≫ pullback.fst f g) (b ≫ pullback.fst f g))
    (h₂ : SSet.Homotopy (a ≫ pullback.snd f g) (b ≫ pullback.snd f g))
    (h : h₁.h ≫ f = h₂.h ≫ g) : SSet.Homotopy a b where
  h := pullback.lift h₁.h h₂.h h
  h₀ := by
    change SSet.ι₀ ≫ pullback.lift h₁.h h₂.h h = a
    apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst] using h₁.h₀
    · simpa only [Category.assoc, pullback.lift_snd] using h₂.h₀
  h₁ := by
    change SSet.ι₁ ≫ pullback.lift h₁.h h₂.h h = b
    apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst] using h₁.h₁
    · simpa only [Category.assoc, pullback.lift_snd] using h₂.h₁
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.2
/-- 第一射影は指定された第一ホモトピーの全時刻を保持する。 -/
lemma roofPullbackHomotopy_fst {K A B C : SSet.{u}} (f : A ⟶ C) (g : B ⟶ C)
    {a b : K ⟶ pullback f g}
    (h₁ : SSet.Homotopy (a ≫ pullback.fst f g) (b ≫ pullback.fst f g))
    (h₂ : SSet.Homotopy (a ≫ pullback.snd f g) (b ≫ pullback.snd f g))
    (h : h₁.h ≫ f = h₂.h ≫ g) :
    (roofPullbackHomotopy f g h₁ h₂ h).h ≫ pullback.fst f g = h₁.h :=
  pullback.lift_fst _ _ _
/-- 第二射影は指定された第二ホモトピーの全時刻を保持する。 -/
lemma roofPullbackHomotopy_snd {K A B C : SSet.{u}} (f : A ⟶ C) (g : B ⟶ C)
    {a b : K ⟶ pullback f g}
    (h₁ : SSet.Homotopy (a ≫ pullback.fst f g) (b ≫ pullback.fst f g))
    (h₂ : SSet.Homotopy (a ≫ pullback.snd f g) (b ≫ pullback.snd f g))
    (h : h₁.h ≫ f = h₂.h ≫ g) :
    (roofPullbackHomotopy f g h₁ h₂ h).h ≫ pullback.snd f g = h₂.h :=
  pullback.lift_snd _ _ _
end SerrePositivity.InfinityCategories.Project.DerivedCategories
