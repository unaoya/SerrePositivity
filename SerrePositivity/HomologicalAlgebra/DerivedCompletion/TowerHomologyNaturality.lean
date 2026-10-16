module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerMap
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerProjection
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.MilnorSequence

/-! # The original Milnor maps are natural for arbitrary tower morphisms -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
variable (R : Type u) [CommRing R]
    {K L : ℕ → CochainComplex (ModuleCat.{u} R) ℤ}
    (t : ∀ n, K (n + 1) ⟶ K n) (s : ∀ n, L (n + 1) ⟶ L n)
    (g : ∀ n, K n ⟶ L n) (hg : ∀ n, t n ≫ g n = g (n + 1) ≫ s n)

lemma complexTowerHomologyShiftEquiv_naturality (i : ℤ)
    (x : (complexTowerHomotopyLimit R K t).homology i) :
    complexTowerHomologyShiftEquiv R L s i
      (HomologicalComplex.homologyMap (complexTowerHomotopyLimitMap R t s g hg) i x) =
        HomologicalComplex.homologyMap
          ((cochainMappingConeFunctor R).map (complexTowerDifferenceArrowMap R t s g hg))
          (i - 1) (complexTowerHomologyShiftEquiv R K t i x) := by
  exact congrArg (fun f => f.hom x)
    ((CochainComplex.ShiftSequence.shiftIso (ModuleCat R) (-1) i (i - 1)
      (by omega)).hom.naturality
        ((cochainMappingConeFunctor R).map (complexTowerDifferenceArrowMap R t s g hg)))

lemma complexTowerProjection_naturality :
    complexTowerHomotopyLimitMap R t s g hg ≫ complexTowerProjection R L s =
      complexTowerProjection R K t ≫ complexTowerProductMap R g := by
  apply HomologicalComplex.hom_ext
  intro n
  simp [complexTowerHomotopyLimitMap, complexTowerProjection,
    CochainComplex.mappingCocone.fst, CochainComplex.HomComplex.Cochain.leftShift,
    CochainComplex.shiftFunctorObjXIso, cochainMappingConeFunctor,
    complexTowerDifferenceArrowMap]
  exact moduleConeArrowMap_fst
    (complexTowerDifference R K t) (complexTowerDifference R L s)
    (complexTowerDifferenceArrowMap R t s g hg) (n + -1) n (by change n + -1 + 1 = n; omega)

lemma complexTowerHomologyIncoming_naturality (i : ℤ)
    (y : ∀ n, (K n).homology (i - 1)) :
    HomologicalComplex.homologyMap (complexTowerHomotopyLimitMap R t s g hg) i
      (complexTowerHomologyIncoming R K t i y) =
        complexTowerHomologyIncoming R L s i
          (fun n => HomologicalComplex.homologyMap (g n) (i - 1) (y n)) := by
  apply (complexTowerHomologyShiftEquiv R L s i).injective
  rw [complexTowerHomologyShiftEquiv_naturality]
  simp only [complexTowerHomologyIncoming, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  have h : CochainComplex.mappingCone.inr (complexTowerDifference R K t) ≫
      (cochainMappingConeFunctor R).map (complexTowerDifferenceArrowMap R t s g hg) =
        complexTowerProductMap R g ≫
          CochainComplex.mappingCone.inr (complexTowerDifference R L s) := by
    apply HomologicalComplex.hom_ext
    intro n
    exact cochainConeArrowMap_inr _ _ _ n
  have hh := congrArg (fun f => HomologicalComplex.homologyMap f (i - 1)) h
  simp only [HomologicalComplex.homologyMap_comp] at hh
  change (HomologicalComplex.homologyMap
    (CochainComplex.mappingCone.inr (complexTowerDifference R K t)) (i - 1) ≫
      HomologicalComplex.homologyMap
        ((cochainMappingConeFunctor R).map (complexTowerDifferenceArrowMap R t s g hg))
        (i - 1)) ((complexProductHomologyEquiv R K (i - 1)).symm y) = _
  rw [hh]
  change HomologicalComplex.homologyMap
    (CochainComplex.mappingCone.inr (complexTowerDifference R L s)) (i - 1)
      (HomologicalComplex.homologyMap (complexTowerProductMap R g) (i - 1)
        ((complexProductHomologyEquiv R K (i - 1)).symm y)) = _
  congr 1
  apply (complexProductHomologyEquiv R L (i - 1)).injective
  ext n
  rw [complexTowerProductMap_homology]
  simp only [LinearEquiv.apply_symm_apply]

lemma complexTowerHomologyBoundary_naturality (i : ℤ)
    (x : (complexTowerHomotopyLimit R K t).homology i) :
    complexTowerHomologyBoundary R L s i
      (HomologicalComplex.homologyMap (complexTowerHomotopyLimitMap R t s g hg) i x) =
        fun n => HomologicalComplex.homologyMap (g n) i
          (complexTowerHomologyBoundary R K t i x n) := by
  rw [complexTowerHomologyBoundary_eq_neg_projection,
    complexTowerHomologyBoundary_eq_neg_projection]
  have h := congrArg (fun f => HomologicalComplex.homologyMap f i)
    (complexTowerProjection_naturality R t s g hg)
  simp only [HomologicalComplex.homologyMap_comp] at h
  ext n
  change -complexProductHomologyEquiv R L i
    (HomologicalComplex.homologyMap (complexTowerProjection R L s) i
      (HomologicalComplex.homologyMap (complexTowerHomotopyLimitMap R t s g hg) i x)) n = _
  have hx := congrArg (fun f => f.hom x) h
  change HomologicalComplex.homologyMap (complexTowerProjection R L s) i
    (HomologicalComplex.homologyMap (complexTowerHomotopyLimitMap R t s g hg) i x) =
      HomologicalComplex.homologyMap (complexTowerProductMap R g) i
        (HomologicalComplex.homologyMap (complexTowerProjection R K t) i x) at hx
  rw [hx, complexTowerProductMap_homology]
  simp only [Pi.neg_apply, map_neg]

end SerrePositivity.DerivedCompletion
