module

public import SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionAdjunction
public import SerrePositivity.InfinityCategories.Core.HomotopyBoundaryExtension
public import SerrePositivity.InfinityCategories.Core.EquivalenceCalculus

/-!
概要：元の prism のホモトピーと厳密な退縮から、亜群化の元の包含を持つ実同値を作る。
方針：prism を内部 Hom の辺へ転置し、全辺局所化後の自然同型に移す。
規約：quasicategory 性は不要。使われ方：端点 fiber の包含の亜群化比較。
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

def functorHomOfPrism {A X : SSet.{u}} {f g : A ⟶ X}
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ X)
    (h₀ : prismEndpoint 0 A ≫ H = f) (h₁ : prismEndpoint 1 A ≫ H = g) : FunctorHom f g := by
  let K : SSet.Homotopy f g := {
    h := (β_ A (Δ[1] : SSet.{u})).hom ≫ H
    h₀ := by
      change prismEndpoint 0 A ≫ H = f
      exact h₀
    h₁ := by
      change prismEndpoint 1 A ≫ H = g
      exact h₁
    rel := by
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro a
      exact False.elim a.1.property }
  exact SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy K)

def groupoidCompletionEquivalenceOfPrismRetraction {A X : SSet.{u}}
    (i : A ⟶ X) (r : X ⟶ A) (hir : i ≫ r = 𝟙 A)
    (H : (Δ[1] : SSet.{u}) ⊗ X ⟶ X)
    (h₀ : prismEndpoint 0 X ≫ H = 𝟙 X) (h₁ : prismEndpoint 1 X ≫ H = r ≫ i) :
    QCatEquivalence (groupoidCompletion A) (groupoidCompletion X) where
  hom := groupoidCompletionMapOf i
  inv := groupoidCompletionMapOf r
  homInvIso := groupoidCompletionMapOf_compIso i r ≪≫
    (by rw [hir]; exact groupoidCompletionMapOf_idIso A)
  invHomIso := groupoidCompletionMapOf_compIso r i ≪≫
    (groupoidCompletionMapOf_functorHomIso (functorHomOfPrism H h₀ h₁)).symm ≪≫
      groupoidCompletionMapOf_idIso X

def groupoidCompletionEquivalenceOfReversePrismRetraction {A X : SSet.{u}}
    (i : A ⟶ X) (r : X ⟶ A) (hir : i ≫ r = 𝟙 A)
    (H : (Δ[1] : SSet.{u}) ⊗ X ⟶ X)
    (h₀ : prismEndpoint 0 X ≫ H = r ≫ i) (h₁ : prismEndpoint 1 X ≫ H = 𝟙 X) :
    QCatEquivalence (groupoidCompletion A) (groupoidCompletion X) where
  hom := groupoidCompletionMapOf i
  inv := groupoidCompletionMapOf r
  homInvIso := groupoidCompletionMapOf_compIso i r ≪≫
    (by rw [hir]; exact groupoidCompletionMapOf_idIso A)
  invHomIso := groupoidCompletionMapOf_compIso r i ≪≫
    groupoidCompletionMapOf_functorHomIso (functorHomOfPrism H h₀ h₁) ≪≫
      groupoidCompletionMapOf_idIso X

lemma prismComparison_groupoidCompletion_isEquivalence {A B X : SSet.{u}}
    (i : A ⟶ X) (j : B ⟶ X) (f : A ⟶ B)
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ X)
    (h₀ : prismEndpoint 0 A ≫ H = i) (h₁ : prismEndpoint 1 A ≫ H = f ≫ j)
    (hi : IsQCatEquivalence (groupoidCompletionMapOf i))
    (hj : IsQCatEquivalence (groupoidCompletionMapOf j)) :
    IsSimplicialHomotopyEquivalence (groupoidCompletionMapOf f) := by
  have h : FunctorIso (groupoidCompletionMapOf f ≫ groupoidCompletionMapOf j)
      (groupoidCompletionMapOf i) :=
    groupoidCompletionMapOf_compIso f j ≪≫
      (groupoidCompletionMapOf_functorHomIso (functorHomOfPrism H h₀ h₁)).symm
  exact (hj.cancel_right (hi.ofFunctorIso h.symm)).isSimplicialHomotopyEquivalence

end SerrePositivity.KST.LocalizingInvariants
