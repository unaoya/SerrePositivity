module
public import SerrePositivity.HomologicalAlgebra.RealizedSingleH0Normalization
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionMonoidal
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! # Tor vanishing inverts the actual tensor augmentation and its completion -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- All higher Tor vanishing makes the original actual tensor augmentation invertible. -/
lemma derivedTensorAugmentation_isIso_of_tor (M N : ModuleCat.{u} R)
    (hTor : ∀ n : ℕ, 0 < n → IsZero (((Tor (ModuleCat R) n).obj M).obj N)) :
    IsIso ((boundedAboveDerivedTensorModuleAugmentation M).app N) := by
  apply (DerivedCategory.isIso_iff (ModuleCat R) _).mpr
  intro i
  by_cases hi : i = 0
  · subst i
    exact derivedTensorAugmentation_h0_isIso M N
  have hX : IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
      ((boundedAboveDerivedTensorModuleFunctor M).obj N)) := by
    by_cases hpos : 0 < i
    · exact DerivedCategory.isZero_of_isLE _ 0 i hpos
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = -(n : ℤ) := by
        exact ⟨(-i).toNat, by omega⟩
      exact ((boundedAboveDerivedTensorModuleTorNatIso M n).app N).isZero_iff.mpr
        (hTor n (by omega))
  have hY : IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
      ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj ((tensorLeft M).obj N))) := by
    by_cases hpos : 0 < i
    · exact DerivedCategory.isZero_of_isLE _ 0 i hpos
    · exact DerivedCategory.isZero_of_isGE _ 0 i (by omega)
  exact hX.isIso hY _

/-- Higher Tor vanishing inverts the underlying derived tensor algebra augmentation. -/
lemma derivedTensorAlgebraAugmentation_isIso_of_tor
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (hTor : ∀ n : ℕ, 0 < n →
      IsZero (((Tor (ModuleCat R) n).obj (ModuleCat.of R S)).obj (ModuleCat.of R T))) :
    IsIso (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T).hom.hom := by
  have : IsIso (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T).hom.hom.hom := by
    rw [boundedAboveDerivedTensorAlgebraAugmentation_hom]
    exact derivedTensorAugmentation_isIso_of_tor (ModuleCat.of R S) (ModuleCat.of R T) hTor
  change IsIso (DerivedCategory.Minus.ι.map
    (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T).hom.hom) at this
  exact isIso_of_reflects_iso
    (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T).hom.hom DerivedCategory.Minus.ι

/-- An invertible underlying derived algebra map gives an equivalence of actual H⁰ algebras. -/
def derivedH0AlgEquivOfIsoUnderlying
    {A B : CommMon (DerivedCategory.Minus (ModuleCat.{u} R))} (f : A ⟶ B)
    (hf : IsIso f.hom.hom) :
    letI := derivedH0CommRing A
    letI := derivedH0CommRing B
    letI := derivedH0Algebra A
    letI := derivedH0Algebra B
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj ≃ₐ[R]
      (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj B.X.obj := by
  letI := derivedH0CommRing A
  letI := derivedH0CommRing B
  letI := derivedH0Algebra A
  letI := derivedH0Algebra B
  have := hf
  have : IsIso f.hom.hom.hom :=
    inferInstanceAs (IsIso (DerivedCategory.Minus.ι.map f.hom.hom))
  have hb := ConcreteCategory.bijective_of_isIso
    ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map f.hom.hom.hom)
  refine AlgEquiv.ofBijective (derivedH0AlgMap f) ?_
  change Function.Bijective (fun x :
      (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj ↦
      (DerivedCategory.homologyFunctor (ModuleCat R) 0).map f.hom.hom.hom x) at hb
  simpa only [← derivedH0AlgMap_apply] using hb

/-- The equivalence uses the original actual H⁰ map without replacing its function. -/
lemma derivedH0AlgEquivOfIsoUnderlying_apply
    {A B : CommMon (DerivedCategory.Minus (ModuleCat.{u} R))} (f : A ⟶ B)
    (hf : IsIso f.hom.hom)
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj) :
    derivedH0AlgEquivOfIsoUnderlying f hf x = derivedH0AlgMap f x := rfl

namespace DerivedCompletion
variable (R) (a : R)

/-- The completed original tensor augmentation is invertible under all higher Tor vanishing. -/
lemma completedTensorAlgebraAugmentation_isIso_of_tor
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (hTor : ∀ n : ℕ, 0 < n →
      IsZero (((Tor (ModuleCat R) n).obj (ModuleCat.of R S)).obj (ModuleCat.of R T))) :
    IsIso (boundedAboveCompletedTensorAlgebraAugmentation R a S T).hom.hom := by
  have := derivedTensorAlgebraAugmentation_isIso_of_tor S T hTor
  change IsIso ((boundedAboveDerivedCompletionFunctor R a).map
    (boundedAboveDerivedTensorAlgebraAugmentation (R := R) S T).hom.hom)
  infer_instance

/-- Complete a Tor-independent tensor to the actual H⁰ algebra of the completed ordinary tensor. -/
def completedTensorH0AlgEquivOfTor
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (hTor : ∀ n : ℕ, 0 < n →
      IsZero (((Tor (ModuleCat R) n).obj (ModuleCat.of R S)).obj (ModuleCat.of R T))) :
    let A := boundedAboveCompletedTensorAlgebra R a S T
    let B := (boundedAboveCompletionCommMonFunctor R a).obj
      (boundedAboveDerivedAlgebra (R := R) (S ⊗[R] T))
    letI := derivedH0CommRing A
    letI := derivedH0CommRing B
    letI := derivedH0Algebra A
    letI := derivedH0Algebra B
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj A.X.obj ≃ₐ[R]
      (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj B.X.obj :=
  derivedH0AlgEquivOfIsoUnderlying (boundedAboveCompletedTensorAlgebraAugmentation R a S T)
    (completedTensorAlgebraAugmentation_isIso_of_tor R a S T hTor)

/-- The Tor comparison is induced by the actual completed standard augmentation. -/
lemma completedTensorH0AlgEquivOfTor_apply
    (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (hTor : ∀ n : ℕ, 0 < n →
      IsZero (((Tor (ModuleCat R) n).obj (ModuleCat.of R S)).obj (ModuleCat.of R T)))
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveCompletedTensorAlgebra R a S T).X.obj) :
    completedTensorH0AlgEquivOfTor R a S T hTor x =
      derivedH0AlgMap (boundedAboveCompletedTensorAlgebraAugmentation R a S T) x := rfl

end DerivedCompletion
end SerrePositivity
