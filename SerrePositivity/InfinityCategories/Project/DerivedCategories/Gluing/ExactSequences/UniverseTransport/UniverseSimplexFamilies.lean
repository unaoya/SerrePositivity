module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedConeSectionEquivalence
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseSSetMaps

/-! 同じ標準単体族を、単体の番号とパラメーターを保って共通宇宙へ移す。 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
variable {K X : SSet.{u}}

def dgGluingUliftSimplexFamily (n : ℕ) (h : (Δ[n] : SSet.{u}) ⊗ K ⟶ X) :
    (Δ[n] : SSet.{max u v}) ⊗ (SSet.uliftFunctor.{v, u}).obj K ⟶
      (SSet.uliftFunctor.{v, u}).obj X :=
  ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} n).inv ▷ (SSet.uliftFunctor.{v, u}).obj K) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso (Δ[n] : SSet.{u}) K).inv ≫ (SSet.uliftFunctor.{v, u}).map h

lemma dgGluingUliftSimplexFamily_restrict {n m : ℕ}
    (h : (Δ[n] : SSet.{u}) ⊗ K ⟶ X) (f : (Δ[m] : SSet.{u}) ⟶ Δ[n])
    (f' : (Δ[m] : SSet.{max u v}) ⟶ Δ[n])
    (hf : f' ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} n).inv =
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} m).inv ≫ (SSet.uliftFunctor.{v, u}).map f) :
    (f' ▷ _) ≫ dgGluingUliftSimplexFamily.{u, v} n h =
      dgGluingUliftSimplexFamily.{u, v} m ((f ▷ K) ≫ h) := by
  rw [dgGluingUliftSimplexFamily, ← comp_whiskerRight_assoc, hf, comp_whiskerRight_assoc]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

lemma dgGluingUliftSimplexFamily_face {n : ℕ}
    (h : (Δ[n + 1] : SSet.{u}) ⊗ K ⟶ X) (i : Fin (n + 2)) :
    (stdSimplex.δ i ▷ _) ≫ dgGluingUliftSimplexFamily.{u, v} (n + 1) h =
      dgGluingUliftSimplexFamily.{u, v} n ((stdSimplex.δ i ▷ K) ≫ h) := by
  apply dgGluingUliftSimplexFamily_restrict
  rfl

lemma dgGluingUliftSimplexFamily_precomp {K' : SSet.{u}} {n : ℕ}
    (h : (Δ[n] : SSet.{u}) ⊗ K ⟶ X) (f : K' ⟶ K) :
    ((Δ[n] : SSet.{max u v}) ◁ (SSet.uliftFunctor.{v, u}).map f) ≫
        dgGluingUliftSimplexFamily.{u, v} n h =
      dgGluingUliftSimplexFamily.{u, v} n (((Δ[n] : SSet.{u}) ◁ f) ≫ h) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
