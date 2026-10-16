module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.BoundedAboveCompletionEquivalence
public import SerrePositivity.HomologicalAlgebra.ConeLES

/-! # Divisibility of homology detected by an actual completion equivalence

If completion inverts f and the target has zero homology in degree i, multiplication
by the completion scalar is surjective on the original source homology in degree i.
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard

/-- A Koszul equivalence detects scalar divisibility in any degree with zero target homology. -/
lemma cochain_homology_smul_surjective_of_koszul_map_quasiIso {R : Type u} [CommRing R] (a : R)
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L)
    (hf : QuasiIso ((scalarConeFunctor a).map f)) (i : ℤ)
    (hL : IsZero (L.homology i)) :
    Function.Surjective (fun x : K.homology i => a • x) := by
  have hn : CochainComplex.mappingCone.inr (smulId a K) ≫ (scalarConeFunctor a).map f =
      f ≫ CochainComplex.mappingCone.inr (smulId a L) := by
    apply HomologicalComplex.Hom.ext
    funext j
    exact scalarConeFunctor_inr_map a f j
  have hh := congrArg (fun g => homologyMap g i) hn
  rw [homologyMap_comp, homologyMap_comp] at hh
  have hzero : homologyMap (CochainComplex.mappingCone.inr (smulId a K)) i = 0 := by
    apply (cancel_mono (homologyMap ((scalarConeFunctor a).map f) i)).mp
    rw [hh]
    simp only [zero_comp]
    rw [hL.eq_of_tgt (homologyMap f i) 0, zero_comp]
  have he := Cone.exact₂ (smulId a K) i
  have hep : Epi (homologyMap (smulId a K) i) := he.epi_f hzero
  have hs := (ModuleCat.epi_iff_surjective _).mp hep
  simp only [smulId, homologyMap_smul, homologyMap_id] at hs
  change Function.Surjective (fun x : K.homology i => a • x) at hs
  exact hs

/-- A completion equivalence gives scalar divisibility on the original actual source homology. -/
lemma boundedAbove_homology_smul_surjective_of_completion_map_isIso
    (R : Type u) [CommRing R] (a : R)
    {X Y : DerivedCategory.Minus (ModuleCat.{u} R)} (f : X ⟶ Y)
    (hf : IsIso ((derivedComplexCompletionFunctor R a).map f.hom)) (i : ℤ)
    (hY : IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj Y.obj)) :
    Function.Surjective
      (fun x : (DerivedCategory.homologyFunctor (ModuleCat R) i).obj X.obj => a • x) := by
  let P := boundedAboveDerivedChosenModel X
  let Q := boundedAboveDerivedChosenModel Y
  let g := P.map Q f.hom
  have hk : IsIso ((derivedScalarConeFunctor R a).map f.hom) := by
    have hi := derivedScalarCone_map_isIso_of_completion R a f.hom hf 1
    rw [pow_one] at hi
    exact hi
  have hg : QuasiIso ((scalarConeFunctor a).map g) := by
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) _).mp
    apply (NatIso.isIso_map_iff (derivedScalarConeComparison R a) g).mp
    change IsIso ((derivedScalarConeFunctor R a).map (DerivedCategory.Q.map g))
    dsimp only [g]
    rw [P.map_Q, Functor.map_comp, Functor.map_comp]
    have := hk
    infer_instance
  let eP := (((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app P.complex).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso P.iso).toLinearEquiv
  let eQ := ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app Q.complex).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso Q.iso
  have hs := cochain_homology_smul_surjective_of_koszul_map_quasiIso a g hg i (hY.of_iso eQ)
  intro x
  obtain ⟨y, hy⟩ := hs (eP.symm x)
  refine ⟨eP y, ?_⟩
  change a • eP y = x
  change a • y = eP.symm x at hy
  rw [← eP.map_smul, hy, eP.apply_symm_apply]

end SerrePositivity.DerivedCompletion
