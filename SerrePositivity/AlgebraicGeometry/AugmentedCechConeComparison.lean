module

public import SerrePositivity.AlgebraicGeometry.CochainAugmentationComparisonForward
public import SerrePositivity.AlgebraicGeometry.CochainAugmentationComparisonBackward
public import SerrePositivity.AlgebraicGeometry.AugmentedCechConeExactnessCriterion

/-!
概要：実際の比較写像に沿い、増大項を含む既存の cone の完全性を比較する。
方針：増大列の要素による両向きの比較を、既存の微分の完全性判定へ渡す。
規約：元の二つの cone、増大写像とその自然性を保持する。
使われ方：共通アフィン細分による射影四角形の全複体の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type v} [CommRing R]

set_option backward.isDefEq.respectTransparency false in
/-- 完全な比較の cone と増大項の全単射に沿い、既存の増大 cone の完全性を比較する。 -/
theorem augmentedCechCone_acyclic_iff_of_comparison
    (A B A' B' : CochainComplex (ModuleCat.{u} R) ℕ) (f : A ⟶ B) (g : A' ⟶ B')
    (Z Z' : ModuleCat.{u} R) (a : Z →ₗ[R] A.X 0) (a' : Z' →ₗ[R] A'.X 0)
    (hc : (cechRefinementConeDifferential A B f 0).comp a = 0)
    (hc' : (cechRefinementConeDifferential A' B' g 0).comp a' = 0)
    (k : cechRefinementCone A B f ⟶ cechRefinementCone A' B' g)
    (ζ : Z →ₗ[R] Z') (hζ : Function.Bijective ζ)
    (haug : (k.f 0).hom.comp a = a'.comp ζ)
    (hk : (cechRefinementCone (cechRefinementCone A B f)
      (cechRefinementCone A' B' g) k).Acyclic) :
    (augmentedCechCone A B f Z a hc).Acyclic ↔
      (augmentedCechCone A' B' g Z' a' hc').Acyclic := by
  let C := cechRefinementCone A B f
  let D := cechRefinementCone A' B' g
  have hC (n : ℕ) : (C.d n (n + 1)).hom = cechRefinementConeDifferential A B f n := by
    dsimp only [C, cechRefinementCone, CochainComplex.of]
    rw [CochainComplex.of_d]
    rfl
  have hD (n : ℕ) : (D.d n (n + 1)).hom = cechRefinementConeDifferential A' B' g n := by
    dsimp only [D, cechRefinementCone, CochainComplex.of]
    rw [CochainComplex.of_d]
    rfl
  have hs : (augmentedCechCone A B f Z a hc).Acyclic ↔
      Function.Injective a ∧ Function.Exact a (C.d 0 1).hom ∧
        ∀ n, Function.Exact (C.d n (n + 1)).hom (C.d (n + 1) (n + 2)).hom := by
    constructor
    · intro h
      obtain ⟨hi, he, hh⟩ :=
        (augmentedCechCone_acyclic_iff_injective_exact A B f Z a hc).mp h
      refine ⟨hi, ?_, ?_⟩
      · rw [hC 0]
        exact he
      · intro n
        change Function.Exact (C.d n (n + 1)).hom (C.d (n + 1) ((n + 1) + 1)).hom
        rw [hC n, hC (n + 1)]
        exact hh n
    · rintro ⟨hi, he, hh⟩
      apply (augmentedCechCone_acyclic_iff_injective_exact A B f Z a hc).mpr
      refine ⟨hi, ?_, ?_⟩
      · rw [hC 0] at he
        exact he
      · intro n
        have he := hh n
        change Function.Exact (C.d n (n + 1)).hom
          (C.d (n + 1) ((n + 1) + 1)).hom at he
        rw [hC n, hC (n + 1)] at he
        exact he
  have ht : (augmentedCechCone A' B' g Z' a' hc').Acyclic ↔
      Function.Injective a' ∧ Function.Exact a' (D.d 0 1).hom ∧
        ∀ n, Function.Exact (D.d n (n + 1)).hom (D.d (n + 1) (n + 2)).hom := by
    constructor
    · intro h
      obtain ⟨hi, he, hh⟩ :=
        (augmentedCechCone_acyclic_iff_injective_exact A' B' g Z' a' hc').mp h
      refine ⟨hi, ?_, ?_⟩
      · rw [hD 0]
        exact he
      · intro n
        change Function.Exact (D.d n (n + 1)).hom (D.d (n + 1) ((n + 1) + 1)).hom
        rw [hD n, hD (n + 1)]
        exact hh n
    · rintro ⟨hi, he, hh⟩
      apply (augmentedCechCone_acyclic_iff_injective_exact A' B' g Z' a' hc').mpr
      refine ⟨hi, ?_, ?_⟩
      · rw [hD 0] at he
        exact he
      · intro n
        have he := hh n
        change Function.Exact (D.d n (n + 1)).hom
          (D.d (n + 1) ((n + 1) + 1)).hom at he
        rw [hD n, hD (n + 1)] at he
        exact he
  have hcycle (z : Z) : (C.d 0 1).hom (a z) = 0 := by
    rw [hC]
    exact LinearMap.congr_fun hc z
  have hcycle' (z : Z') : (D.d 0 1).hom (a' z) = 0 := by
    rw [hD]
    exact LinearMap.congr_fun hc' z
  rw [hs, ht]
  constructor
  · rintro ⟨hi, he, hd⟩
    exact cochainAugmentation_exact_of_comparison C D k Z Z' a a' ζ hζ haug hcycle' hk hi he hd
  · rintro ⟨hi, he, hd⟩
    exact cochainAugmentation_exact_reflected_of_comparison C D k Z Z' a a' ζ hζ haug
      hcycle hk hi he hd

end SerrePositivity.AlgebraicGeometry
