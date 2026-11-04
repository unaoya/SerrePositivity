module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Tower.Milnor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Koszul.Tower
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Koszul の完備化の H⁰ の Milnor 列

## 概要

商環の逆極限への全射 `koszulCompletionH0Projection` を作り、その核に負の次数のホモロジーの lim¹ を保つ短完全列（`koszulCompletionH0MilnorSequence`）を与える。錐の連結射の符号を正規化した射影が、標準の包含を商の標準写像へ送ることを示す。

## 方針

Tower/Milnor の一般の Milnor 列を Koszul の塔に当てる。

## 規約

環構造・導来完備性・普遍性はこの完全列とは別に示す。旧 `KoszulMilnor`・`KoszulUnitCompatibility`。

## 使われ方

`Principal/*`・`Pair/*`。
-/

@[expose] public noncomputable section

universe u

section KoszulMilnorPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
variable (R : Type u) [CommRing R]

/-- 各冪の商環の遷移をR線形写像として使う。 -/
def powerKoszulQuotientTransitionLinear {e : ℕ} (a : Fin e → R) (n : ℕ) :
    R ⧸ powerKoszulIdeal R a (n + 1) →ₗ[R] R ⧸ powerKoszulIdeal R a n :=
  (Ideal.Quotient.factorₐ R (powerKoszulIdeal_antitone R a (Nat.le_succ n))).toLinearMap

/-- H⁰の逆極限と、標準商環列の逆極限との正規化された線形同型。 -/
def powerKoszulH0LimitEquiv {e : ℕ} (a : Fin e → R) :
    moduleTowerLimit R (fun n ↦ (powerKoszulTower R a n).homology 0)
      (fun n ↦ (HomologicalComplex.homologyMap (powerKoszulTransition R a n) 0).hom) ≃ₗ[R]
    moduleTowerLimit R (fun n ↦ R ⧸ powerKoszulIdeal R a n)
      (powerKoszulQuotientTransitionLinear R a) where
  toFun x := ⟨fun n ↦ powerKoszulStageH0Equiv R a n (x.val n), by
    apply (mem_moduleTowerLimit_iff R _ _ _).mpr
    intro n
    change powerKoszulQuotientTransition R a n
      (powerKoszulStageH0Equiv R a (n + 1) (x.val (n + 1))) = _
    rw [← powerKoszulStageH0Equiv_transition]
    exact congrArg (powerKoszulStageH0Equiv R a n)
      ((mem_moduleTowerLimit_iff R _ _ _).mp x.property n)⟩
  invFun x := ⟨fun n ↦ (powerKoszulStageH0Equiv R a n).symm (x.val n), by
    apply (mem_moduleTowerLimit_iff R _ _ _).mpr
    intro n
    apply (powerKoszulStageH0Equiv R a n).injective
    rw [powerKoszulStageH0Equiv_transition, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]
    exact (mem_moduleTowerLimit_iff R _ _ _).mp x.property n⟩
  left_inv x := by apply Subtype.ext; funext n; exact LinearEquiv.symm_apply_apply _ _
  right_inv x := by apply Subtype.ext; funext n; exact LinearEquiv.apply_symm_apply _ _
  map_add' x y := by apply Subtype.ext; funext n; exact map_add _ _ _
  map_smul' r x := by apply Subtype.ext; funext n; exact map_smul _ _ _

/-- 完備化候補のH⁰から標準商環列の逆極限への線形写像。
標準三角形の連結射の負を使い、標準包含の元を保つ符号に正規化する。 -/
def koszulCompletionH0Projection {e : ℕ} (a : Fin e → R) :
    (koszulCompletionComplex R a).homology 0 →ₗ[R]
      moduleTowerLimit R (fun n ↦ R ⧸ powerKoszulIdeal R a n)
        (powerKoszulQuotientTransitionLinear R a) :=
  -((powerKoszulH0LimitEquiv R a).toLinearMap.comp
    (complexTowerMilnorProjection R (powerKoszulTower R a) (powerKoszulTransition R a) 0))

/-- 標準商環列の逆極限への写像は全射。単射性は主張しない。 -/
theorem koszulCompletionH0Projection_surjective {e : ℕ} (a : Fin e → R) :
    Function.Surjective (koszulCompletionH0Projection R a) := by
  intro y
  obtain ⟨x, hx⟩ := (powerKoszulH0LimitEquiv R a).surjective.comp
    (complexTowerMilnorProjection_surjective R (powerKoszulTower R a)
      (powerKoszulTransition R a) 0) (-y)
  change (powerKoszulH0LimitEquiv R a)
    (complexTowerMilnorProjection R (powerKoszulTower R a)
      (powerKoszulTransition R a) 0 x) = -y at hx
  exact ⟨x, by change -((powerKoszulH0LimitEquiv R a) _) = y; rw [hx, neg_neg]⟩

/-- KoszulのH⁰のMilnor列。左端はH⁻¹の差分の余核。 -/
def koszulCompletionH0MilnorSequence {e : ℕ} (a : Fin e → R) :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk
    (complexTowerMilnorInclusion R (powerKoszulTower R a) (powerKoszulTransition R a) 0)
    (koszulCompletionH0Projection R a) (by
      rw [koszulCompletionH0Projection, LinearMap.neg_comp, LinearMap.comp_assoc,
        complexTowerMilnor_comp, LinearMap.comp_zero, neg_zero])

/-- 0 → lim¹ H⁻¹(K_n) → H⁰(holim K_n) → lim R/(a₁ⁿ,…,aₑⁿ) → 0。 -/
theorem koszulCompletionH0MilnorSequence_shortExact {e : ℕ} (a : Fin e → R) :
    (koszulCompletionH0MilnorSequence R a).ShortExact where
  exact := by
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro x hx
    have hx' : complexTowerMilnorProjection R (powerKoszulTower R a)
        (powerKoszulTransition R a) 0 x = 0 := by
      apply (powerKoszulH0LimitEquiv R a).injective
      exact (neg_eq_zero.mp hx).trans (map_zero _).symm
    exact (ShortComplex.moduleCat_exact_iff _).mp
      (complexTowerMilnorSequence_shortExact R (powerKoszulTower R a)
        (powerKoszulTransition R a) 0).exact x hx'
  mono_f := (ModuleCat.mono_iff_injective _).mpr
    (complexTowerMilnorInclusion_injective R (powerKoszulTower R a)
      (powerKoszulTransition R a) 0)
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (koszulCompletionH0Projection_surjective R a)

/-- H⁰のKoszul逆系の差分は全射。H⁻¹については仮定しない。 -/
theorem powerKoszulHomologyDifference_zero_surjective {e : ℕ} (a : Fin e → R) :
    Function.Surjective (complexTowerHomologyDifference R (powerKoszulTower R a)
      (powerKoszulTransition R a) 0) :=
  moduleTowerDifference_surjective R _ _ (powerKoszulTransition_homology_zero_surjective R a)

/-- Koszul完備化候補の正次数ホモロジーは零。 -/
theorem koszulCompletionComplex_isZero_homology_of_pos {e : ℕ} (a : Fin e → R)
    (i : ℤ) (hi : 0 < i) : IsZero ((koszulCompletionComplex R a).homology i) := by
  have hdiff : Function.Surjective (complexTowerHomologyDifference R (powerKoszulTower R a)
      (powerKoszulTransition R a) (i - 1)) := by
    by_cases h : i - 1 = 0
    · rw [h]
      exact powerKoszulHomologyDifference_zero_surjective R a
    · apply moduleTowerDifference_surjective
      intro n x
      have hz := koszulComplex_isZero_homology_of_pos (fun j ↦ a j ^ n) (i - 1) (by omega)
      have hsub := ModuleCat.isZero_iff_subsingleton.mp hz
      exact ⟨0, hsub.elim _ _⟩
  have hinj := complexTowerMilnorProjection_injective_of_surjective R (powerKoszulTower R a)
    (powerKoszulTransition R a) i hdiff
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun x y ↦ ?_⟩
  apply hinj
  apply Subtype.ext
  funext n
  exact (ModuleCat.isZero_iff_subsingleton.mp
    (koszulComplex_isZero_homology_of_pos (fun j ↦ a j ^ n) i hi)).elim _ _

end SerrePositivity.DerivedCompletion

end KoszulMilnorPart

section KoszulUnitCompatibilityPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
variable (R : Type u) [CommRing R]

/-- 元の環から完備化候補のH⁰への、標準包含に誘導される線形写像。 -/
def koszulCompletionH0Unit {e : ℕ} (a : Fin e → R) :
    R →ₗ[R] (koszulCompletionComplex R a).homology 0 :=
  (HomologicalComplex.homologyMap (koszulCompletionUnit R a) 0).hom.comp
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
      (ModuleCat.of R R)).inv.hom

/-- 正規化したH⁰射影は、実際の複体の各段への射影から計算できる。 -/
theorem koszulCompletionH0Projection_apply {e : ℕ} (a : Fin e → R)
    (x : (koszulCompletionComplex R a).homology 0) (n : ℕ) :
    (koszulCompletionH0Projection R a x).val n =
      powerKoszulStageH0Equiv R a n
        (HomologicalComplex.homologyMap
          (complexTowerProjection R (powerKoszulTower R a) (powerKoszulTransition R a) ≫
            Pi.π (powerKoszulTower R a) n) 0 x) := by
  change -(powerKoszulStageH0Equiv R a n
    (complexTowerHomologyBoundary R (powerKoszulTower R a) (powerKoszulTransition R a) 0 x n)) = _
  rw [complexTowerHomologyBoundary_eq_neg_projection]
  simp only [Pi.neg_apply, map_neg, neg_neg, complexProductHomologyEquiv_apply,
    HomologicalComplex.homologyMap_comp]
  rfl

/-- 元の環の元は、各冪の商環でその標準的な剰余類へ送られる。 -/
@[simp] theorem koszulCompletionH0Projection_unit_apply {e : ℕ} (a : Fin e → R)
    (r : R) (n : ℕ) :
    (koszulCompletionH0Projection R a (koszulCompletionH0Unit R a r)).val n =
      Ideal.Quotient.mk (powerKoszulIdeal R a n) r := by
  rw [koszulCompletionH0Projection_apply]
  have h := congrArg (fun f ↦ HomologicalComplex.homologyMap f 0)
    (koszulCompletionUnit_comp_projection R a n)
  rw [HomologicalComplex.homologyMap_comp] at h
  have hr := congrArg (fun f ↦ f.hom
    ((HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
      (ModuleCat.of R R)).inv.hom r)) h
  change HomologicalComplex.homologyMap
    (complexTowerProjection R (powerKoszulTower R a) (powerKoszulTransition R a) ≫
      Pi.π (powerKoszulTower R a) n) 0 (koszulCompletionH0Unit R a r) =
        koszulH0Unit R (fun i ↦ a i ^ n) r at hr
  rw [hr, powerKoszulStageH0Equiv_unit]

/-- 元の環から標準商環列の逆極限への線形写像。 -/
def powerKoszulQuotientLimitUnit {e : ℕ} (a : Fin e → R) :
    R →ₗ[R] moduleTowerLimit R (fun n ↦ R ⧸ powerKoszulIdeal R a n)
      (powerKoszulQuotientTransitionLinear R a) :=
  moduleTowerLimitLift R _ _ R (fun n ↦ (powerKoszulIdeal R a n).mkQ)
    (fun n ↦ by apply LinearMap.ext; intro r; rfl)

/-- 標準包含、H⁰射影、商環列の標準写像の図式は可換。 -/
theorem koszulCompletionH0Projection_comp_unit {e : ℕ} (a : Fin e → R) :
    (koszulCompletionH0Projection R a).comp (koszulCompletionH0Unit R a) =
      powerKoszulQuotientLimitUnit R a := by
  apply LinearMap.ext
  intro r
  apply Subtype.ext
  funext n
  exact koszulCompletionH0Projection_unit_apply R a r n

end SerrePositivity.DerivedCompletion

end KoszulUnitCompatibilityPart
