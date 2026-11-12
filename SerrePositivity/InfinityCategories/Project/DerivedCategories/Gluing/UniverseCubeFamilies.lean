module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseSimplexFamilies
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath

/-! 同じ二・三重区間族を共通宇宙へ移し、全時間・全パラメータと三方向の面を保持する。 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial

def dgGluingUliftPrismDomain (K : SSet.{u}) :
    (Δ[1] : SSet.{max u v}) ⊗ (SSet.uliftFunctor.{v, u}).obj K ⟶
      (SSet.uliftFunctor.{v, u}).obj ((Δ[1] : SSet.{u}) ⊗ K) :=
  ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} 1).inv ▷ (SSet.uliftFunctor.{v, u}).obj K) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso (Δ[1] : SSet.{u}) K).inv

def dgGluingUliftSquareDomain (K : SSet.{u}) :
    (Δ[1] : SSet.{max u v}) ⊗ (Δ[1] ⊗ (SSet.uliftFunctor.{v, u}).obj K) ⟶
      (SSet.uliftFunctor.{v, u}).obj ((Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ K)) :=
  (Δ[1] ◁ dgGluingUliftPrismDomain.{u, v} K) ≫
    dgGluingUliftPrismDomain.{u, v} (Δ[1] ⊗ K)

variable {K X : SSet.{u}}

def dgGluingUliftSquareFamily (h : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ K) ⟶ X) :
    (Δ[1] : SSet.{max u v}) ⊗ (Δ[1] ⊗ (SSet.uliftFunctor.{v, u}).obj K) ⟶
      (SSet.uliftFunctor.{v, u}).obj X :=
  (Δ[1] ◁ dgGluingUliftPrismDomain.{u, v} K) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily.{u, v} 1 h

def dgGluingUliftCubeFamily (h : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ (Δ[1] ⊗ K)) ⟶ X) :
    (Δ[1] : SSet.{max u v}) ⊗ (Δ[1] ⊗ (Δ[1] ⊗ (SSet.uliftFunctor.{v, u}).obj K)) ⟶
      (SSet.uliftFunctor.{v, u}).obj X :=
  (Δ[1] ◁ dgGluingUliftSquareDomain.{u, v} K) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily.{u, v} 1 h

lemma dgGluingUliftCubeFamily_outer
    (h : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ (Δ[1] ⊗ K)) ⟶ X) (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i _ ≫ dgGluingUliftCubeFamily.{u, v} h =
      dgGluingUliftSquareFamily.{u, v} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i _ ≫ h) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

lemma dgGluingUliftCubeFamily_middle
    (h : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ (Δ[1] ⊗ K)) ⟶ X) (i : Fin 2) :
    (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i _) ≫ dgGluingUliftCubeFamily.{u, v} h =
      dgGluingUliftSquareFamily.{u, v} ((Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i _) ≫ h) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

lemma dgGluingUliftCubeFamily_inner
    (h : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ (Δ[1] ⊗ K)) ⟶ X) (i : Fin 2) :
    (Δ[1] ◁ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i _)) ≫ dgGluingUliftCubeFamily.{u, v} h =
      dgGluingUliftSquareFamily.{u, v} ((Δ[1] ◁ (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i _)) ≫ h) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

lemma dgGluingUliftCubeFamily_precomp {L : SSet.{u}}
    (h : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ (Δ[1] ⊗ K)) ⟶ X) (f : L ⟶ K) :
    (Δ[1] ◁ (Δ[1] ◁ (Δ[1] ◁ (SSet.uliftFunctor.{v, u}).map f))) ≫
        dgGluingUliftCubeFamily.{u, v} h =
      dgGluingUliftCubeFamily.{u, v} ((Δ[1] ◁ (Δ[1] ◁ (Δ[1] ◁ f))) ≫ h) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

lemma dgGluingUliftCubeFamily_post {Y : SSet.{u}}
    (h : (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ (Δ[1] ⊗ K)) ⟶ X) (q : X ⟶ Y) :
    dgGluingUliftCubeFamily.{u, v} h ≫ (SSet.uliftFunctor.{v, u}).map q =
      dgGluingUliftCubeFamily.{u, v} (h ≫ q) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
