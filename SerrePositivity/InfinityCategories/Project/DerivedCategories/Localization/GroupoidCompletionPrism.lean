module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionAdjunction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.HomotopyBoundaryExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceCalculus

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization
open _root_.SerrePositivity.KST.LocalizingInvariants

def functorHomOfPrism {A X : SSet.{u}} {f g : A ⟶ X}
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ X)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H = f) (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ H = g) : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g := by
  let K : SSet.Homotopy f g := {
    h := (β_ A (Δ[1] : SSet.{u})).hom ≫ H
    h₀ := by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H = f
      exact h₀
    h₁ := by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ H = g
      exact h₁
    rel := by
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro a
      exact False.elim a.1.property }
  exact SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy K)

def groupoidCompletionEquivalenceOfPrismRetraction {A X : SSet.{u}}
    (i : A ⟶ X) (r : X ⟶ A) (hir : i ≫ r = 𝟙 A)
    (H : (Δ[1] : SSet.{u}) ⊗ X ⟶ X)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 X ≫ H = 𝟙 X) (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 X ≫ H = r ≫ i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion A) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion X) where
  hom := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf i
  inv := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf r
  homInvIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf_compIso i r ≪≫
    (by rw [hir]; exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf_idIso A)
  invHomIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf_compIso r i ≪≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf_functorHomIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.functorHomOfPrism H h₀ h₁)).symm ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf_idIso X

def groupoidCompletionEquivalenceOfReversePrismRetraction {A X : SSet.{u}}
    (i : A ⟶ X) (r : X ⟶ A) (hir : i ≫ r = 𝟙 A)
    (H : (Δ[1] : SSet.{u}) ⊗ X ⟶ X)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 X ≫ H = r ≫ i) (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 X ≫ H = 𝟙 X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion A) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion X) where
  hom := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf i
  inv := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf r
  homInvIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf_compIso i r ≪≫
    (by rw [hir]; exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf_idIso A)
  invHomIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf_compIso r i ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf_functorHomIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.functorHomOfPrism H h₀ h₁) ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf_idIso X

lemma prismComparison_groupoidCompletion_isEquivalence {A B X : SSet.{u}}
    (i : A ⟶ X) (j : B ⟶ X) (f : A ⟶ B)
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ X)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H = i) (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ H = f ≫ j)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf i))
    (hj : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf j)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf f) := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf j)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf i) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf_compIso f j ≪≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionMapOf_functorHomIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.functorHomOfPrism H h₀ h₁)).symm
  exact (hj.cancel_right (hi.ofFunctorIso h.symm)).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.functorHomOfPrism (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.functorHomOfPrism := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.functorHomOfPrism

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionEquivalenceOfPrismRetraction (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.groupoidCompletionEquivalenceOfPrismRetraction := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionEquivalenceOfPrismRetraction

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionEquivalenceOfReversePrismRetraction (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.groupoidCompletionEquivalenceOfReversePrismRetraction := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionEquivalenceOfReversePrismRetraction

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.prismComparison_groupoidCompletion_isEquivalence := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.prismComparison_groupoidCompletion_isEquivalence

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.functorHomOfPrism._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.functorHomOfPrism._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.functorHomOfPrism._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.functorHomOfPrism._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.functorHomOfPrism._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.functorHomOfPrism._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.functorHomOfPrism._proof_4 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.functorHomOfPrism._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.groupoidCompletionEquivalenceOfPrismRetraction._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.groupoidCompletionEquivalenceOfPrismRetraction._proof_1
