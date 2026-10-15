module
public import SerrePositivity.HomologicalAlgebra.CochainLinearDualConeNaturality
public import SerrePositivity.HomologicalAlgebra.KoszulLinearDuality
public import SerrePositivity.PerfectComplex.ConeArrowMap

/-! # Naturality of the standard scalar cone and shift comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex
variable {R : Type u} [CommRing R]
variable {P Q P' Q' : CochainComplex (ModuleCat.{u} R) ℤ}

/-- Shift a commutative square of cochain maps. -/
abbrev mappingConeShiftArrow (φ : P ⟶ Q) (ψ : P' ⟶ Q')
    (α : Arrow.mk φ ⟶ Arrow.mk ψ) (m : ℤ) : Arrow.mk (φ⟦m⟧') ⟶ Arrow.mk (ψ⟦m⟧') :=
  Arrow.homMk (α.left⟦m⟧') (α.right⟦m⟧') (by
    simpa only [Functor.map_comp, Arrow.mk_hom, Arrow.mk_left, Arrow.mk_right] using
      congrArg ((CategoryTheory.shiftFunctor _ m).map) α.w)

/-- The standard cone-shift isomorphism respects the actual map of cones. -/
lemma mappingConeShiftIso_naturality (φ : P ⟶ Q) (ψ : P' ⟶ Q')
    (α : Arrow.mk φ ⟶ Arrow.mk ψ) (m : ℤ) :
    (cochainConeArrowMap φ ψ α)⟦m⟧' ≫ (mappingCone.shiftIso ψ m).hom =
      (mappingCone.shiftIso φ m).hom ≫
        cochainConeArrowMap (φ⟦m⟧') (ψ⟦m⟧') (mappingConeShiftArrow φ ψ α m) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply mappingCone.ext_to (ψ⟦m⟧') i (i + 1) rfl
  · simp only [HomologicalComplex.comp_f, Category.assoc,
      cochainConeArrowMap_fst, mappingCone.shiftIso,
      mappingCone.lift_f_fst_v, mappingCone.lift_f_fst_v_assoc,
      Cocycle.coe_units_smul, Cocycle.shift_coe, CochainComplex.HomComplex.Cochain.units_smul_v,
      CochainComplex.HomComplex.Cochain.shift_v', shiftFunctor_map_f']
    have hn := DerivedCompletion.moduleConeArrowMap_fst φ ψ α (i + m) (i + 1 + m)
      (by change i + m + 1 = i + 1 + m; omega)
    change (cochainConeArrowMap φ ψ α).f (i + m) ≫
        (mappingCone.fst ψ).1.v (i + m) (i + 1 + m) (by omega) =
      (mappingCone.fst φ).1.v (i + m) (i + 1 + m) (by omega) ≫ α.left.f (i + 1 + m) at hn
    simpa only [mappingConeShiftArrow, Arrow.homMk_left, shiftFunctor_map_f',
      Linear.comp_units_smul, Linear.units_smul_comp] using congrArg (fun g => m.negOnePow • g) hn
  · simp only [HomologicalComplex.comp_f, Category.assoc,
      cochainConeArrowMap_snd, mappingCone.shiftIso,
      mappingCone.lift_f_snd_v, mappingCone.lift_f_snd_v_assoc,
      CochainComplex.HomComplex.Cochain.shift_v', shiftFunctor_map_f']
    rfl

/-- Transporting shifted scalar arrows preserves the actual scalar cone maps. -/
lemma scalarConeShift_eqToHom (a : R) {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : K ⟶ L) (m : ℤ) :
    cochainConeArrowMap ((smulId a K)⟦m⟧') ((smulId a L)⟦m⟧')
        (mappingConeShiftArrow (smulId a K) (smulId a L) (Arrow.homMk f f (by simp [smulId])) m) ≫
        eqToHom (show mappingCone ((smulId a L)⟦m⟧') = (scalarConeFunctor a).obj (L⟦m⟧) by
          have he : (smulId a L)⟦m⟧' = smulId a (L⟦m⟧) := by simp [smulId, Functor.map_smul]
          rw [he]; rfl) =
      eqToHom (show mappingCone ((smulId a K)⟦m⟧') = (scalarConeFunctor a).obj (K⟦m⟧) by
          have he : (smulId a K)⟦m⟧' = smulId a (K⟦m⟧) := by simp [smulId, Functor.map_smul]
          rw [he]; rfl) ≫ (scalarConeFunctor a).map (f⟦m⟧') := by
  exact mappingConeArrowMap_eqToHom _ _ _ _
    (show (smulId a K)⟦m⟧' = smulId a (K⟦m⟧) by simp [smulId, Functor.map_smul])
    (show (smulId a L)⟦m⟧' = smulId a (L⟦m⟧) by simp [smulId, Functor.map_smul])
    (mappingConeShiftArrow (smulId a K) (smulId a L) (Arrow.homMk f f (by simp [smulId])) m)
    (Arrow.homMk (f⟦m⟧') (f⟦m⟧') (by simp [smulId])) rfl rfl

/-- Scalar cone and shift comparison is natural in arbitrary cochain maps. -/
lemma scalarConeShiftIso_naturality (a : R) {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : K ⟶ L) (m : ℤ) :
    ((scalarConeFunctor a).map f)⟦m⟧' ≫ (scalarConeShiftIso a L m).hom =
      (scalarConeShiftIso a K m).hom ≫ (scalarConeFunctor a).map (f⟦m⟧') := by
  have h := scalarConeShift_eqToHom a f m
  dsimp only [scalarConeShiftIso, Iso.trans_hom, eqToIso.hom]
  rw [← Category.assoc]
  erw [mappingConeShiftIso_naturality (smulId a K) (smulId a L)
    (Arrow.homMk f f (by simp [smulId])) m]
  simpa only [Category.assoc, eqToHom_refl, Category.comp_id, Category.id_comp] using congrArg
    (fun g => (mappingCone.shiftIso (smulId a K) m).hom ≫ g) h

end SerrePositivity
