module
public import SerrePositivity.KTheory.HomologyPeeling

/-! # The supported K₀/G₀ comparison is an isomorphism -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits HomologicalComplex
variable {R : Type u} [CommRing R]

namespace K0WithSupport
lemma mk_complex_shift (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hp : strictlyPerfectComplex R P)
    (hs : HasHomologySupportOn Z P) (n : ℤ) :
    mk Z (supportedPerfectOnObj Z (P⟦n⟧) (strictlyPerfectComplex_shift hp n) (hs.shift n)) =
      ((n.negOnePow : ℤˣ) : ℤ) • mk Z (supportedPerfectOnObj Z P hp hs) := by
  let X := supportedPerfectOnObj Z P hp hs
  let Y := supportedPerfectOnObj Z (P⟦n⟧) (strictlyPerfectComplex_shift hp n) (hs.shift n)
  let I := supportedPerfectAmbient Z
  have e : I.obj Y ≅ I.obj (X⟦n⟧) :=
    ((HomotopyCategory.quotient _ _).commShiftIso n).app P ≪≫ ((I.commShiftIso n).app X).symm
  have h := mk_iso Z (I.preimageIso e)
  exact h.trans (mk_shift Z X n)
end K0WithSupport

variable [IsNoetherianRing R] [HasFiniteProjectiveResolutions R]
  (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
/-- The difference between the resolution/Euler composite and the identity. -/
def comparisonDefect : K0WithSupport Z →+ K0WithSupport Z :=
  (G0WithSupport.resolutionMap Z).comp (K0WithSupport.homologyEuler Z) - AddMonoidHom.id _

lemma comparisonDefect_resolution (M : SupportedFGModuleOn Z) (F : PerfectModuleResolution M.obj) :
    comparisonDefect Z (F.k0Class Z M.property.2) = 0 := by
  simp only [comparisonDefect, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply,
    K0WithSupport.homologyEuler_resolution, G0WithSupport.resolutionMap_mk,
    AddMonoidHom.id_apply, resClass_eq M F, sub_self]

/-- The homology interval is the induction measure, not the interval of nonzero terms. -/
lemma comparisonDefect_zero_of_homology_width (n : ℕ) :
    ∀ (P : CochainComplex (ModuleCat.{u} R) ℤ) (hp : strictlyPerfectComplex R P)
      (hs : HasHomologySupportOn Z P) (a b : ℤ),
      (∀ i, i < a ∨ b < i → IsZero (P.homology i)) → b - a < (n : ℤ) →
      comparisonDefect Z (K0WithSupport.mk Z (supportedPerfectOnObj Z P hp hs)) = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro P hp hs a b hb hw
    by_cases hab : b < a
    · have hac : ∀ i, IsZero (P.homology i) := fun i => hb i (by omega)
      rw [K0WithSupport.mk_eq_zero_of_acyclic Z hp hs
        (fun i => (P.exactAt_iff_isZero_homology i).mpr (hac i)), map_zero]
    · let S := P⟦b⟧
      let hsp := strictlyPerfectComplex_shift hp b
      let hss := hs.shift b
      have hS (i : ℤ) (hi : i < a - b ∨ 0 < i) : IsZero (S.homology i) := by
        have hP : IsZero (P.homology (b + i)) := hb _ (by omega)
        exact hP.of_iso
          (((HomologicalComplex.homologyFunctor _ (.up ℤ) 0).shiftIso b i (b + i) rfl).app P)
      obtain ⟨F, l, hl⟩ := exists_topResolutionMap S hsp (fun i hi => hS i (Or.inr hi))
      let C := CochainComplex.mappingCone l
      let hc := strictlyPerfectComplex_mappingCone R l hsp F.perfect
      have : Module.Finite R (S.homology 0) := by
        have := (hsp.2 0).1
        exact homology_moduleFinite S 0
      let M : SupportedFGModuleOn Z := ⟨S.homology 0, inferInstance, hss 0⟩
      let hf := F.support M.property.2
      let hcs := hss.mappingCone l hf
      have hCb : ∀ i : ℤ, i < (a - b) - 1 ∨ -2 < i → IsZero (C.homology i) :=
        topResolutionCone_homology_bounded S (a - b)
          (fun i hi => hS i (Or.inl hi)) (fun i hi => hS i (Or.inr hi)) F l hl
      have hCzero : comparisonDefect Z
          (K0WithSupport.mk Z (supportedPerfectOnObj Z C hc hcs)) = 0 :=
        ih (n - 1) (by omega) C hc hcs ((a - b) - 1) (-2) hCb (by omega)
      have hFzero := comparisonDefect_resolution Z M F
      have hcone := K0WithSupport.mk_cone Z S F.complex hsp F.perfect hss hf l
      have hd := congrArg (comparisonDefect Z) hcone
      rw [map_sub, hCzero] at hd
      change 0 = comparisonDefect Z (F.k0Class Z M.property.2) -
        comparisonDefect Z (K0WithSupport.mk Z (supportedPerfectOnObj Z S hsp hss)) at hd
      rw [hFzero, zero_sub] at hd
      have hSz : comparisonDefect Z (K0WithSupport.mk Z (supportedPerfectOnObj Z S hsp hss)) = 0 :=
        neg_eq_zero.mp hd.symm
      rw [K0WithSupport.mk_complex_shift Z P hp hs b, map_zsmul] at hSz
      have h := congrArg (fun x : K0WithSupport Z => ((b.negOnePow⁻¹ : ℤˣ) : ℤ) • x) hSz
      simpa only [smul_zero, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        one_smul] using h

lemma comparisonDefect_complex_zero (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) (hs : HasHomologySupportOn Z P) :
    comparisonDefect Z (K0WithSupport.mk Z (supportedPerfectOnObj Z P hp hs)) = 0 := by
  obtain ⟨a, b, ha, hb⟩ := hp.1
  have hH : ∀ i, i < a ∨ b < i → IsZero (P.homology i) := by
    intro i hi
    exact isZero_homology_of_isZero_X P i
      (hi.elim (fun h => P.isZero_of_isStrictlyGE a i h)
        (fun h => P.isZero_of_isStrictlyLE b i h))
  apply comparisonDefect_zero_of_homology_width Z ((b - a).toNat + 1) P hp hs a b hH
  omega

namespace K0WithSupport
/-- The other inverse identity, proved by homology-width induction. -/
lemma resolutionMap_homologyEuler :
    (G0WithSupport.resolutionMap Z).comp (homologyEuler Z) = AddMonoidHom.id (K0WithSupport Z) := by
  have hz : comparisonDefect Z = 0 := by
    apply hom_ext Z
    intro X
    obtain ⟨P : CochainComplex (ModuleCat.{u} R) ℤ, hP⟩ := X.obj.obj.quotient_obj_surjective
    have hp : strictlyPerfectComplex R P := by
      apply (perfectHomotopyProperty_quotient R P).mp
      rw [hP]
      exact X.obj.property
    have hs : HasHomologySupportOn Z P := by
      apply (perfectHomotopyObj_supportedOn_iff Z P hp).mp
      intro q
      change Module.support R ((HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (.up ℤ) q).obj
        ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj P)) ⊆ Z
      rw [hP]
      exact X.property q
    let I := supportedPerfectAmbient Z
    have e : X ≅ supportedPerfectOnObj Z P hp hs := I.preimageIso (eqToIso hP.symm)
    change comparisonDefect Z (mk Z X) = 0
    rw [mk_iso Z e]
    exact comparisonDefect_complex_zero Z P hp hs
  exact sub_eq_zero.mp hz
end K0WithSupport

/-- The supported resolution and homology Euler maps are mutually inverse. -/
def k0G0WithSupportEquiv : K0WithSupport Z ≃+ G0WithSupport Z where
  toFun := K0WithSupport.homologyEuler Z
  invFun := G0WithSupport.resolutionMap Z
  left_inv x := DFunLike.congr_fun (K0WithSupport.resolutionMap_homologyEuler Z) x
  right_inv x := DFunLike.congr_fun (K0WithSupport.homologyEuler_resolutionMap Z) x
  map_add' := map_add _

omit [HasFiniteProjectiveResolutions R] in
/-- The homology Euler summands of a perfect object have finite support. -/
lemma supportedHomologyEuler_hasFiniteSupport (X : SupportedPerfectHomotopyOn Z) :
    Function.HasFiniteSupport (fun q : ℤ => ((q.negOnePow : ℤˣ) : ℤ) •
      G0WithSupport.mk (supportedPerfectHomology Z X q)) := by
  obtain ⟨a, b, hab⟩ := supportedPerfectHomology_bounded Z X
  apply (Set.finite_Icc a b).subset
  intro q hq
  by_contra hn
  exact hq (by
    change ((q.negOnePow : ℤˣ) : ℤ) • G0WithSupport.mk (supportedPerfectHomology Z X q) = 0
    rw [G0WithSupport.mk_of_isZero _
      (hab q (by simp only [Set.mem_Icc] at hn; omega)), smul_zero])

/-- A perfect class is the alternating sum of its homology resolution classes. -/
lemma k0Class_eq_sum_resolutionClasses (X : SupportedPerfectHomotopyOn Z) :
    K0WithSupport.mk Z X = ∑ᶠ q : ℤ, ((q.negOnePow : ℤˣ) : ℤ) •
      resClass (supportedPerfectHomology Z X q) := by
  have h := DFunLike.congr_fun (K0WithSupport.resolutionMap_homologyEuler Z)
    (K0WithSupport.mk Z X)
  change G0WithSupport.resolutionMap Z (K0WithSupport.homologyEuler Z (K0WithSupport.mk Z X)) =
    K0WithSupport.mk Z X at h
  rw [K0WithSupport.homologyEuler_mk] at h
  unfold supportedHomologyEuler supportedModuleEuler at h
  rw [(G0WithSupport.resolutionMap Z).map_finsum (supportedHomologyEuler_hasFiniteSupport Z X)] at h
  simpa only [map_zsmul, G0WithSupport.resolutionMap_mk] using h.symm

end SerrePositivity
