module
public import SerrePositivity.BhattScholze.Perfectoidization.WittPresentation.FontaineCompletedTensorDiscrete
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedTensorZero

/-! # Discreteness and perfectoid H⁰ of the original completed tensor of perfectoid algebras -/
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard

/-- The original completed tensor is discrete and its actual H⁰ ring is perfectoid.
No p-regularity, finiteness, nonzero, or flatness conditions are added. -/
lemma integralPerfectoid_completedTensor_pure_and_h0
    (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hT : IsIntegralPerfectoid T p) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    ((boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj.IsGE 0 ∧
      (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj.IsLE 0) ∧
      IsIntegralPerfectoid ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
        (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj) p := by
  let ORIG := boundedAboveCompletedTensorAlgebra R (p : R) S T
  letI := derivedH0CommRing ORIG
  have hzpure (hz : IsZero ORIG.X.obj) : ORIG.X.obj.IsGE 0 ∧ ORIG.X.obj.IsLE 0 := by
    exact ⟨(DerivedCategory.isGE_iff _ _).mpr (fun i _ =>
      (DerivedCategory.homologyFunctor (ModuleCat R) i).map_isZero hz),
      (DerivedCategory.isLE_iff _ _).mpr (fun i _ =>
        (DerivedCategory.homologyFunctor (ModuleCat R) i).map_isZero hz)⟩
  have hzresults (hz : IsZero ORIG.X.obj) :
      (ORIG.X.obj.IsGE 0 ∧ ORIG.X.obj.IsLE 0) ∧
        IsIntegralPerfectoid ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
          ORIG.X.obj) p := by
    exact ⟨hzpure hz, Or.inl (ModuleCat.isZero_iff_subsingleton.mp
      ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map_isZero hz))⟩
  rcases subsingleton_or_nontrivial S with hs0 | hs1
  · exact hzresults (completedTensor_isZero_of_left_isZero R (p : R)
      (ModuleCat.of R S) (ModuleCat.of R T) (ModuleCat.isZero_iff_subsingleton.mpr hs0))
  · letI := hs1
    rcases subsingleton_or_nontrivial T with ht0 | ht1
    · exact hzresults (completedTensor_isZero_of_right_isZero R (p : R)
        (ModuleCat.of R S) (ModuleCat.of R T) (ModuleCat.isZero_iff_subsingleton.mpr ht0))
    · letI := ht1
      letI : Nontrivial R := (algebraMap R S).domain_nontrivial
      rcases hR with hzero | ⟨hpR, hcR, ⟨π, u, hpEq⟩, hFR, hkerR⟩
      · letI := hzero
        exact (zero_ne_one (Subsingleton.elim (0 : R) 1)).elim
      rcases hS with hzero | ⟨hpS, hcS, _, hFS, hkerS⟩
      · letI := hzero
        exact (zero_ne_one (Subsingleton.elim (0 : S) 1)).elim
      rcases hT with hzero | ⟨hpT, hcT, _, hFT, hkerT⟩
      · letI := hzero
        exact (zero_ne_one (Subsingleton.elim (0 : T) 1)).elim
      letI : Fact (¬ IsUnit (p : R)) := ⟨hpR⟩
      letI : Fact (¬ IsUnit (p : S)) := ⟨hpS⟩
      letI : Fact (¬ IsUnit (p : T)) := ⟨hpT⟩
      letI := hcR
      letI := hcS
      letI := hcT
      obtain ⟨d, hd, hk⟩ := exists_distinguished_fontaine_kernel_generator R p
        hFR hkerR π u hpEq
      exact fontaine_completedTensor_pure_and_h0 p R S T d hd hk hFR hFS hFT hkerS hkerT

/-- The original public discreteness statement is retained. -/
lemma integralPerfectoid_completedTensor_pure
    (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hT : IsIntegralPerfectoid T p) :
    (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj.IsGE 0 ∧
      (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj.IsLE 0 := by
  exact (integralPerfectoid_completedTensor_pure_and_h0 p R S T hR hS hT).1

/-- The actual original completed tensor H⁰ ring is integral perfectoid, without
regularity, bounded-torsion, flatness, or nonzero assumptions on the factors. -/
lemma integralPerfectoid_completedTensorH0_isIntegralPerfectoid
    (p : ℕ) [Fact p.Prime] (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hT : IsIntegralPerfectoid T p) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    IsIntegralPerfectoid ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj) p := by
  exact (integralPerfectoid_completedTensor_pure_and_h0 p R S T hR hS hT).2

end SerrePositivity.BhattScholze
