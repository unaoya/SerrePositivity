module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerProjection
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.KoszulMilnor

/-! # Koszul完備化のH⁰の標準写像と商環列への射影

錐の連結射の符号を正規化した射影が、標準包含を商の標準写像へ送ることを証明する。
-/

@[expose] public noncomputable section
universe u
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
