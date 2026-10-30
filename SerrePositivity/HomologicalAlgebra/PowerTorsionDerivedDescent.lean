module
public import SerrePositivity.HomologicalAlgebra.DerivedAcyclicHomology
public import SerrePositivity.HomologicalAlgebra.DerivedHomologyLinear
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.PowerTorsion

/-! # Homology descent along completely faithfully flat maps for power-torsion objects -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- Ordinary scalar extension reflects zero maps on power-torsion modules. -/
lemma completelyFaithfullyFlat_extendScalars_map_eq_zero_iff (a : R)
    (hS : IsCompletelyFaithfullyFlat (Ideal.span {a}) (baseChangeScalarModule φ)) (n : ℕ)
    {M N : ModuleCat.{u} R} (hM : ∀ x : M, a ^ n • x = 0)
    (hN : ∀ x : N, a ^ n • x = 0) (f : M ⟶ N) :
    (ModuleCat.extendScalars φ).map f = 0 ↔ f = 0 := by
  constructor
  · intro h
    algebraize [φ]
    have hS' : IsCompletelyFaithfullyFlat (Ideal.span {a}) S := hS
    have hz : LinearMap.lTensor S f.hom = 0 := by
      apply LinearMap.ext
      intro x
      exact congrArg (fun k => k.hom x) h
    apply ModuleCat.hom_ext
    exact (power_torsion_ordinary_lTensor_eq_zero_iff a S hS' n hM hN f.hom).mp hz
  · rintro rfl
    exact Functor.map_zero _ _ _

/-- Complete flatness makes all power-torsion actual cohomology modules Tor-acyclic. -/
lemma homologyTorAcyclic_of_power_torsion (a : R)
    (hS : IsCompletelyFlat (Ideal.span {a}) (baseChangeScalarModule φ)) (n : ℕ)
    (X : DerivedCategory.Minus (ModuleCat.{u} R))
    (hX : ∀ i : ℤ, ∀ x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj X.obj,
      a ^ n • x = 0) : homologyTorAcyclic φ X.obj := by
  intro i k hk
  have hs : Subsingleton (((Tor (ModuleCat R) k).obj (baseChangeScalarModule φ)).obj
      ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj X.obj)) :=
    torModule_subsingleton_of_completelyFlat_powerTorsion a (baseChangeScalarModule φ)
      hS n ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj X.obj) (hX i) k hk
  exact ModuleCat.isZero_of_subsingleton _

/-- Derived scalar extension reflects zero homology maps for power-torsion cohomology. -/
lemma powerTorsionDerivedHomology_map_eq_zero_iff (a : R)
    (hS : IsCompletelyFaithfullyFlat (Ideal.span {a}) (baseChangeScalarModule φ)) (n : ℕ)
    {X Y : DerivedCategory.Minus (ModuleCat.{u} R)}
    (hX : ∀ i : ℤ, ∀ x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj X.obj,
      a ^ n • x = 0)
    (hY : ∀ i : ℤ, ∀ x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj Y.obj,
      a ^ n • x = 0) (f : X ⟶ Y) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat S) i).map
        ((boundedAboveDerivedBaseChange φ).map f).hom = 0 ↔
      (DerivedCategory.homologyFunctor (ModuleCat R) i).map f.hom = 0 :=
  (boundedAboveDerivedHomology_map_eq_zero_iff φ
      (homologyTorAcyclic_of_power_torsion φ a hS.1 n X hX)
      (homologyTorAcyclic_of_power_torsion φ a hS.1 n Y hY) f i).trans
    (completelyFaithfullyFlat_extendScalars_map_eq_zero_iff φ a hS n (hX i) (hY i) _)

/-- Scalar zero maps are reflected as actual pointwise annihilation of the original homology. -/
lemma powerTorsionDerivedHomology_scalar_eq_zero_iff (a : R)
    (hS : IsCompletelyFaithfullyFlat (Ideal.span {a}) (baseChangeScalarModule φ)) (n : ℕ)
    (X : DerivedCategory.Minus (ModuleCat.{u} R))
    (hX : ∀ i : ℤ, ∀ x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj X.obj,
      a ^ n • x = 0) (g : R) (N : ℕ) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat S) i).map
        ((boundedAboveDerivedBaseChange φ).map (g ^ N • 𝟙 X)).hom = 0 ↔
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj X.obj, g ^ N • x = 0 := by
  rw [powerTorsionDerivedHomology_map_eq_zero_iff φ a hS n hX hX]
  change (DerivedCategory.homologyFunctor (ModuleCat R) i).map (g ^ N • 𝟙 X.obj) = 0 ↔ _
  rw [Functor.map_smul, CategoryTheory.Functor.map_id]
  constructor
  · intro h x
    exact congrArg (fun f => f.hom x) h
  · intro h
    ext x
    exact h x

/-- The usual scalar-extension map sends original scalar multiplication to the target scalar. -/
lemma extendScalars_scalar_id (M : ModuleCat.{u} R) (r : R) :
    (ModuleCat.extendScalars φ).map (r • 𝟙 M) =
      φ r • 𝟙 ((ModuleCat.extendScalars φ).obj M) := by
  algebraize [φ]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul s x =>
    change S at s
    change s ⊗ₜ[R] (r • x) = (φ r * s) ⊗ₜ[R] x
    rw [TensorProduct.tmul_smul]
    rfl
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- Target scalar annihilation after ordinary extension is faithfully reflected on power torsion. -/
lemma powerTorsion_extendScalars_annihilated_iff (a : R)
    (hS : IsCompletelyFaithfullyFlat (Ideal.span {a}) (baseChangeScalarModule φ)) (n : ℕ)
    (M : ModuleCat.{u} R) (hM : ∀ x : M, a ^ n • x = 0) (r : R) :
    (∀ x : (ModuleCat.extendScalars φ).obj M, φ r • x = 0) ↔ ∀ x : M, r • x = 0 := by
  have he := completelyFaithfullyFlat_extendScalars_map_eq_zero_iff φ a hS n hM hM (r • 𝟙 M)
  rw [extendScalars_scalar_id] at he
  have hleft : (φ r • 𝟙 ((ModuleCat.extendScalars φ).obj M) = 0) ↔
      ∀ x : (ModuleCat.extendScalars φ).obj M, φ r • x = 0 := by
    constructor
    · intro h x; exact congrArg (fun f => f.hom x) h
    · intro h
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact h x
  have hright : (r • 𝟙 M = 0) ↔ ∀ x : M, r • x = 0 := by
    constructor
    · intro h x; exact congrArg (fun f => f.hom x) h
    · intro h
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact h x
  exact hleft.symm.trans (he.trans hright)

/-- Actual scalar annihilation of derived-image homology is reflected before base change. -/
lemma powerTorsionDerivedHomology_annihilated_iff (a : R)
    (hS : IsCompletelyFaithfullyFlat (Ideal.span {a}) (baseChangeScalarModule φ)) (n : ℕ)
    (X : DerivedCategory.Minus (ModuleCat.{u} R))
    (hX : ∀ i : ℤ, ∀ x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj X.obj,
      a ^ n • x = 0) (r : R) (i : ℤ) :
    (∀ x : (DerivedCategory.homologyFunctor (ModuleCat S) i).obj
        ((boundedAboveDerivedBaseChange φ).obj X).obj, φ r • x = 0) ↔
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj X.obj, r • x = 0 := by
  let e := boundedAboveDerivedBaseChangeHomologyIso φ X
    (homologyTorAcyclic_of_power_torsion φ a hS.1 n X hX) i
  have hh : (∀ x : (DerivedCategory.homologyFunctor (ModuleCat S) i).obj
        ((boundedAboveDerivedBaseChange φ).obj X).obj, φ r • x = 0) ↔
      ∀ x : (ModuleCat.extendScalars φ).obj
        ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj X.obj), φ r • x = 0 := by
    rw [← Module.mem_annihilator, ← Module.mem_annihilator, e.toLinearEquiv.annihilator_eq]
  exact hh.trans (powerTorsion_extendScalars_annihilated_iff φ a hS n _ (hX i) r)

/-- A single scalar exponent is preserved for an entire family of power-torsion objects. -/
lemma powerTorsionDerivedHomology_uniform_annihilated_iff (a : R)
    (hS : IsCompletelyFaithfullyFlat (Ideal.span {a}) (baseChangeScalarModule φ))
    (X : ℕ → DerivedCategory.Minus (ModuleCat.{u} R))
    (hX : ∀ n : ℕ, ∀ i : ℤ,
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj (X n).obj, a ^ n • x = 0)
    (g : R) (degrees : Set ℤ) :
    (∃ N : ℕ, ∀ n : ℕ, ∀ i ∈ degrees,
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat S) i).obj
        ((boundedAboveDerivedBaseChange φ).obj (X n)).obj, (φ g) ^ N • x = 0) ↔
      ∃ N : ℕ, ∀ n : ℕ, ∀ i ∈ degrees,
        ∀ x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj (X n).obj, g ^ N • x = 0 := by
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, fun n i hi => ?_⟩
    apply (powerTorsionDerivedHomology_annihilated_iff φ a hS n (X n) (hX n) (g ^ N) i).mp
    simpa only [map_pow] using hN n i hi
  · rintro ⟨N, hN⟩
    refine ⟨N, fun n i hi => ?_⟩
    have h := (powerTorsionDerivedHomology_annihilated_iff φ a hS n (X n) (hX n) (g ^ N) i).mpr
      (hN n i hi)
    simpa only [map_pow] using h

end SerrePositivity
