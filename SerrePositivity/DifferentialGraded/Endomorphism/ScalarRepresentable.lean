module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarHomFactors

/-! # 実際の代表加群と係数変更の一致 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex CochainComplex HomComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] (z : D)

lemma scalarRepresentable_eq :
    ScalarExtension.rightModule φ D (representable A z) =
      representable A' (show ScalarExtension.DGBaseChange φ D from z) := by
  let := φ.toAlgebra
  apply EnrichedFunctor.ext (Complex A')
    (F := (ScalarExtension.rightModule φ D (representable A z)).toFunctor)
    (G := (representable A' (show ScalarExtension.DGBaseChange φ D from z)).toFunctor)
    (fun _ => rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  apply HomologicalComplex.hom_ext
  intro p
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply Cochain.ext
  intro r n hn
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change ((ScalarExtension.homComparison φ _ _).f p
    ((ModuleCat.extendScalars φ).map (((representable A z).map x y).f p)
      ((1 : A') ⊗ₜ[A] f))).v r n hn ((1 : A') ⊗ₜ[A] m) = _
  erw [ModuleCat.ExtendScalars.map_tmul φ, ScalarExtension.homComparison_apply]
  change (1 : A') ⊗ₜ[A] forward A (D := D) f m (by omega) =
    forward A' (D := ScalarExtension.DGBaseChange φ D)
      ((1 : A') ⊗ₜ[A] f) ((1 : A') ⊗ₜ[A] m) (by omega)
  exact (endomorphismScalarForward_one φ D f m (by omega)).symm

end SerrePositivity.DifferentialGraded
