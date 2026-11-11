module

public import SerrePositivity.KST.LocalizingInvariants.DiagramFamilyTranspose

/-!
概要：関手正方形を時間付きの矢印族へ転置し、四辺を厳密に回収する。
方針：区間・パラメータ・時間をパラメータ・区間・時間へ並べ替えて curry する。
規約：四つの代表ホモトピーを保持。使われ方：実 lax pullback の単位への持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
namespace FunctorSquareArrowFamily

/-- 区間・パラメータ・時間の三座標の並べ替え。 -/
def shape (A : SSet.{u}) :
    (Δ[1] : SSet.{u}) ⊗ (A ⊗ Δ[1]) ⟶ A ⊗ (Δ[1] ⊗ Δ[1]) where
  app _ := ↾fun p ↦ (p.2.1, (p.1, p.2.2))
  naturality {_ _} _ := rfl

variable {A X : SSet.{u}} {U₀ U₁ V₀ V₁ : A ⟶ X}
  {b : SSet.Homotopy U₀ U₁} {t : SSet.Homotopy V₀ V₁}
  {l : SSet.Homotopy U₀ V₀} {r : SSet.Homotopy U₁ V₁}
  (s : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomSquare b t l r)

/-- 四辺を持つ元の関手正方形の、時間付きの矢印族。 -/
def family : A ⊗ (Δ[1] : SSet.{u}) ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  curry (shape A ≫ uncurry s.diagram)

lemma source : family s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = l.h := by
  rw [family, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨a, z⟩
  have h := congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ (ihom A).obj X =>
    (uncurry f).app n (a, z)) s.left
  rw [uncurry_natural_left, uncurry_curry] at h
  change (uncurry s.diagram).app n (a,
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[1] : SSet.{u})).app n z) = l.h.app n (a, z) at h
  exact h

lemma target : family s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = r.h := by
  rw [family, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨a, z⟩
  have h := congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ (ihom A).obj X =>
    (uncurry f).app n (a, z)) s.right
  rw [uncurry_natural_left, uncurry_curry] at h
  change (uncurry s.diagram).app n (a,
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[1] : SSet.{u})).app n z) = r.h.app n (a, z) at h
  exact h

lemma zero : (SSet.ι₀ : A ⟶ A ⊗ (Δ[1] : SSet.{u})) ≫ family s =
    ZeroArrowFamily.ofHomotopy b := by
  apply uncurry_injective
  rw [uncurry_natural_left, family, uncurry_curry,
    ZeroArrowFamily.ofHomotopy, uncurry_curry]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨e, a⟩
  have h := congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ (ihom A).obj X =>
    (uncurry f).app n (a, e)) s.bottom
  rw [uncurry_natural_left, uncurry_curry] at h
  change (uncurry s.diagram).app n (a,
    (SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]).app n e) = b.h.app n (a, e) at h
  exact h

lemma one : (SSet.ι₁ : A ⟶ A ⊗ (Δ[1] : SSet.{u})) ≫ family s =
    ZeroArrowFamily.ofHomotopy t := by
  apply uncurry_injective
  rw [uncurry_natural_left, family, uncurry_curry,
    ZeroArrowFamily.ofHomotopy, uncurry_curry]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨e, a⟩
  have h := congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ (ihom A).obj X =>
    (uncurry f).app n (a, e)) s.top
  rw [uncurry_natural_left, uncurry_curry] at h
  change (uncurry s.diagram).app n (a,
    (SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]).app n e) = t.h.app n (a, e) at h
  exact h

end FunctorSquareArrowFamily
end SerrePositivity.KST.LocalizingInvariants
