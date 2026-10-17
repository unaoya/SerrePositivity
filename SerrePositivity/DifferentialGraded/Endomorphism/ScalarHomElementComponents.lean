module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarHomElements

/-! # Hom要素の係数拡大と各評価cochainの一致 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

lemma scalarHomComparison_one_eq_map {K L : Complex A} {p : ℤ} (f : Cochain K L p) :
    let := φ.toAlgebra
    (ScalarExtension.homComparison φ K L).f p ((1 : A') ⊗ₜ[A] f) =
      f.map (ModuleCat.extendScalars φ) := by
  let := φ.toAlgebra
  apply Cochain.ext
  intro i j h
  apply ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((ScalarExtension.homComparison φ K L).f p ((1 : A') ⊗ₜ[A] f)).v i j h
      ((1 : A') ⊗ₜ[A] x) =
    (ModuleCat.extendScalars φ).map (f.v i j h) ((1 : A') ⊗ₜ[A] x)
  erw [ScalarExtension.homComparison_apply φ K L p i j h f x,
    ModuleCat.ExtendScalars.map_tmul φ]

variable (D : Type v) [DGCategory A D] [Small.{u} D]

lemma scalarModuleHomElement_π_map {M N : RightModule A D} {p : ℤ}
    (f : GradedHom A M N p) (x : D) :
    (moduleHomπ A' (ScalarExtension.DGBaseChange φ D)
      (ScalarExtension.rightModule φ D M) (ScalarExtension.rightModule φ D N) x).f p
        (scalarModuleHomElement φ D f) =
      ((moduleHomπ A D M N x).f p f).map (ModuleCat.extendScalars φ) := by
  let := φ.toAlgebra
  have h := congrArg (fun k => k.f p ((1 : A') ⊗ₜ[A] f)) (scalarModuleHom_π φ D M N x)
  change _ = (ScalarExtension.homComparison φ (M.obj (Opposite.op x))
      (N.obj (Opposite.op x))).f p
    ((ModuleCat.extendScalars φ).map ((moduleHomπ A D M N x).f p) ((1 : A') ⊗ₜ[A] f)) at h
  erw [ModuleCat.ExtendScalars.map_tmul φ] at h
  exact h.trans (scalarHomComparison_one_eq_map φ ((moduleHomπ A D M N x).f p f))

end SerrePositivity.DifferentialGraded
