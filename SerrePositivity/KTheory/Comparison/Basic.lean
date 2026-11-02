module

public import SerrePositivity.KTheory.HomologyEulerBasic
public import SerrePositivity.KTheory.Comparison.ResolutionClass
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import SerrePositivity.KTheory.LocalizationCoefficients

/-! # 台つき K₀ と G₀ の比較

## 概要

台つき分解のホモロジーの Euler 類を定め、厳密に完全な複体の最上段のホモロジーをはがす議論で、台つき K₀ から G₀ への比較写像が同型であることと、その自然性を示す。

## 方針

良い切り詰めは中間の対象としてだけ使い、K 射影性で擬逆を持ち上げる。

## 規約

比較の自然性は `enlarge` 版と `map` 版が二重にあり、一本化は保留（refactor-plan §6.2.3）。

## 使われ方

KTheory/Adams、交点重複度の Adams 作用素による消滅。
-/

@[expose] public noncomputable section

universe u

section HomologyEulerPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Limits Pretriangulated
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  (Z : TopologicalSpace.Closeds (PrimeSpectrum R))

namespace K0WithSupport
lemma homologyEuler_resolution (M : SupportedFGModuleOn Z) (F : PerfectModuleResolution M.obj) :
    homologyEuler Z (F.k0Class Z M.property.2) = G0WithSupport.mk M := by
  rw [PerfectModuleResolution.k0Class, homologyEuler_mk]
  unfold supportedHomologyEuler supportedModuleEuler
  rw [finsum_eq_single _ (0 : ℤ)]
  · simp only [Int.negOnePow_zero, Units.val_one, one_smul]
    apply G0WithSupport.mk_iso
    exact (HomotopyCategory.homologyFunctorFactors _ _ 0).app F.complex ≪≫
      F.resolution.homologyZeroIso
  · intro q hq
    rw [G0WithSupport.mk_of_isZero _ ?_, smul_zero]
    exact (F.resolution.isZero_homology q hq).of_iso
      ((HomotopyCategory.homologyFunctorFactors _ _ q).app F.complex)

variable [HasFiniteProjectiveResolutions R]
lemma homologyEuler_resolutionMap : (homologyEuler Z).comp (G0WithSupport.resolutionMap Z) =
    AddMonoidHom.id (G0WithSupport Z) := by
  apply G0WithSupport.hom_ext
  intro M
  simp only [AddMonoidHom.comp_apply, G0WithSupport.resolutionMap_mk, AddMonoidHom.id_apply]
  exact homologyEuler_resolution Z M (chosenPerfectModuleResolution M.obj)
end K0WithSupport
end SerrePositivity

end HomologyEulerPart

section HomologyPeelingPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Limits HomologicalComplex
variable {R : Type u} [CommRing R]

/-- A perfect complex with no positive homology maps to its H⁰ with identity on H⁰. -/
lemma exists_topHomologyMap (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) (hpos : ∀ i : ℤ, 0 < i → IsZero (P.homology i)) :
    ∃ g : P ⟶ (HomologicalComplex.single _ (.up ℤ) 0).obj (P.homology 0),
      homologyMap g 0 ≫ (singleObjHomologySelfIso _ 0 (P.homology 0)).hom = 𝟙 _ := by
  have : P.IsKProjective := strictlyPerfectComplex_isKProjective hp
  have : P.IsLE 0 := (P.isLE_iff 0).mpr
    (fun i hi => (P.exactAt_iff_isZero_homology i).mpr (hpos i hi))
  let Q := P.truncLE 0
  let i := P.ιTruncLE 0
  have : QuasiIso i := (P.quasiIso_ιTruncLE_iff 0).mpr inferInstance
  obtain ⟨f, ⟨H⟩⟩ := exists_lift_of_quasiIso i (𝟙 P)
  have htop : ∀ j : ℤ, 0 < j → IsZero (Q.X j) := fun j hj => Q.isZero_of_isStrictlyLE 0 j hj
  let a := toSingleOfHomology Q (d_zero_one_eq_zero Q htop) (homologyMap i 0)
  refine ⟨f ≫ a, ?_⟩
  have ha := toSingleOfHomology_homologyMap Q (d_zero_one_eq_zero Q htop) (homologyMap i 0)
  rw [homologyMap_comp, Category.assoc, ha, ← homologyMap_comp, H.homologyMap_eq, homologyMap_id]

variable [IsNoetherianRing R] [HasFiniteProjectiveResolutions R]
/-- Lift the top-homology map to a perfect resolution, making H⁰ an isomorphism. -/
lemma exists_topResolutionMap (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) (hpos : ∀ i : ℤ, 0 < i → IsZero (P.homology i)) :
    ∃ (F : PerfectModuleResolution (P.homology 0)) (l : P ⟶ F.complex),
      homologyMap l 0 ≫ F.resolution.homologyZeroIso.hom = 𝟙 _ := by
  have := (hp.2 0).1
  have : Module.Finite R (P.homology 0) := homology_moduleFinite P 0
  let F := chosenPerfectModuleResolution (P.homology 0)
  obtain ⟨g, hg⟩ := exists_topHomologyMap P hp hpos
  have : P.IsKProjective := strictlyPerfectComplex_isKProjective hp
  obtain ⟨l, ⟨H⟩⟩ := exists_lift_of_quasiIso F.augmentation g
  refine ⟨F, l, ?_⟩
  have ha := toSingleOfHomology_homologyMap F.complex
    (d_zero_one_eq_zero _ F.resolution.isZero_X) F.resolution.homologyZeroIso.hom
  calc
    homologyMap l 0 ≫ F.resolution.homologyZeroIso.hom =
        homologyMap l 0 ≫ homologyMap F.augmentation 0 ≫
          (singleObjHomologySelfIso _ 0 (P.homology 0)).hom := by
      simpa only [PerfectModuleResolution.augmentation, Category.assoc] using
        congrArg (fun k => homologyMap l 0 ≫ k) ha.symm
    _ = homologyMap g 0 ≫ (singleObjHomologySelfIso _ 0 (P.homology 0)).hom := by
      rw [← Category.assoc, ← homologyMap_comp, H.homologyMap_eq]
    _ = 𝟙 _ := hg

omit [IsNoetherianRing R] [HasFiniteProjectiveResolutions R] in
/-- Peeling H⁰ decreases the homology interval even if the terms of the cone grow. -/
lemma topResolutionCone_homology_bounded
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ)
    (hbelow : ∀ i : ℤ, i < a → IsZero (P.homology i))
    (hpos : ∀ i : ℤ, 0 < i → IsZero (P.homology i))
    (F : PerfectModuleResolution (P.homology 0)) (l : P ⟶ F.complex)
    (hl : homologyMap l 0 ≫ F.resolution.homologyZeroIso.hom = 𝟙 _) :
    ∀ i : ℤ, i < a - 1 ∨ -2 < i → IsZero ((CochainComplex.mappingCone l).homology i) := by
  have he : homologyMap l 0 = F.resolution.homologyZeroIso.inv := by
    apply (cancel_mono F.resolution.homologyZeroIso.hom).mp
    rw [hl, Iso.inv_hom_id]
  have : IsIso (homologyMap l 0) := by rw [he]; infer_instance
  intro i hi
  by_cases hi' : i = -1
  · subst i
    have h10 : (-1 : ℤ) + 1 = 0 := by norm_num
    have hδ : Cone.δ l (-1) 0 h10 = 0 :=
      (Cone.exact₁ l (-1) 0 h10).mono_g_iff.mp inferInstance
    exact (Cone.exact₃ l (-1) 0 h10).isZero_X₂
      ((F.resolution.isZero_homology (-1) (by norm_num)).eq_zero_of_src _) hδ
  · by_cases hi0 : i = 0
    · subst i
      have hι : homologyMap (CochainComplex.mappingCone.inr l) 0 = 0 :=
        (Cone.exact₂ l 0).epi_f_iff.mp inferInstance
      exact (Cone.exact₃ l 0 1 rfl).isZero_X₂ hι ((hpos 1 one_pos).eq_zero_of_tgt _)
    · apply (Cone.exact₃ l i (i + 1) rfl).isZero_of_both_isZero
      · exact F.resolution.isZero_homology i hi0
      · rcases hi with hi | hi
        · exact hbelow _ (by omega)
        · exact hpos _ (by omega)

end SerrePositivity

end HomologyPeelingPart

section ComparisonInversePart

set_option backward.isDefEq.respectTransparency false
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

end ComparisonInversePart

section ComparisonNaturalityPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Limits
variable {R S : Type u} [CommRing R] [CommRing S]

namespace PerfectModuleResolution
/-- Flat base change of any strictly perfect module resolution. -/
def baseChange (φ : R →+* S) (hf : φ.Flat) {M : ModuleCat.{u} R}
    (F : PerfectModuleResolution M) :
    PerfectModuleResolution ((ModuleCat.extendScalars φ).obj M) := by
  algebraize [φ]
  have : Module.Flat R S := hf
  let hS := isResolutionOf_baseChange_of_flat R S M F.resolution
  let e := moduleCatBaseChangeTensorEquiv (R := R) (B := S) M
  refine ⟨SerrePositivity.baseChange φ F.complex, ?_,
    strictlyPerfectComplex_baseChange φ F.complex F.perfect⟩
  exact { hS with homologyZeroIso := hS.homologyZeroIso ≪≫ e.symm.toModuleIso }
end PerfectModuleResolution

/-- The proved finite-projective resolution contract is stable under any localization. -/
lemma hasFiniteProjectiveResolutions_of_localization [Algebra R S]
    (P : Submonoid R) [IsLocalization P S] [IsNoetherianRing R]
    [HasFiniteProjectiveResolutions R] : HasFiniteProjectiveResolutions S where
  exists_resolution M h := by
    have := h
    obtain ⟨M₀, hfinite, _, ⟨e⟩⟩ := exists_finitePresentation_descent P M
    have := hfinite
    obtain ⟨F, ⟨hF⟩, hp⟩ := HasFiniteProjectiveResolutions.exists_resolution M₀
    let G := PerfectModuleResolution.baseChange (algebraMap R S)
      (by rw [RingHom.flat_algebraMap_iff]; exact IsLocalization.flat S P)
      (⟨F, hF, hp⟩ : PerfectModuleResolution M₀)
    let e' := (moduleCatBaseChangeTensorEquiv (R := R) (B := S) M₀).trans e
    exact ⟨G.complex, ⟨{G.resolution with
      homologyZeroIso := G.resolution.homologyZeroIso ≪≫ e'.toModuleIso}⟩, G.perfect⟩

variable [IsNoetherianRing R] [IsNoetherianRing S]
  [HasFiniteProjectiveResolutions R] [HasFiniteProjectiveResolutions S]

omit [IsNoetherianRing R] in
lemma resClass_enlarge {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)} (h : Z ≤ W)
    (M : SupportedFGModuleOn Z) :
    K0WithSupport.enlarge h (resClass M) = resClass (M.enlarge h) := by
  let F := chosenPerfectModuleResolution M.obj
  rw [resClass_eq M F, resClass_eq (M.enlarge h) F]
  unfold PerfectModuleResolution.k0Class
  rw [K0WithSupport.enlarge_mk]
  apply K0WithSupport.mk_iso
  exact ObjectProperty.isoMk _ (Iso.refl _)

omit [IsNoetherianRing R] [IsNoetherianRing S] in
lemma resClass_map (φ : R →+* S) (hf : φ.Flat)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W : TopologicalSpace.Closeds (PrimeSpectrum S)) (h : supportPullback φ Z ≤ W)
    (M : SupportedFGModuleOn Z) :
    K0WithSupport.map φ Z W h (resClass M) = resClass (M.baseChange φ Z W h) := by
  let F := chosenPerfectModuleResolution M.obj
  let G := F.baseChange φ hf
  rw [resClass_eq M F, resClass_eq (M.baseChange φ Z W h) G]
  unfold PerfectModuleResolution.k0Class
  rw [K0WithSupport.map_mk]
  apply K0WithSupport.mk_iso
  exact ObjectProperty.isoMk _ (ObjectProperty.isoMk _ (Iso.refl _))

namespace G0WithSupport
omit [IsNoetherianRing R] in
lemma resolutionMap_enlarge {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)} (h : Z ≤ W) :
    (K0WithSupport.enlarge h).comp (resolutionMap Z) = (resolutionMap W).comp (enlarge h) := by
  apply hom_ext
  intro M
  simp only [AddMonoidHom.comp_apply, resolutionMap_mk, enlarge_mk]
  exact resClass_enlarge h M

omit [IsNoetherianRing R] [IsNoetherianRing S] in
lemma resolutionMap_map (φ : R →+* S) (hf : φ.Flat)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W : TopologicalSpace.Closeds (PrimeSpectrum S)) (h : supportPullback φ Z ≤ W) :
    (K0WithSupport.map φ Z W h).comp (resolutionMap Z) =
      (resolutionMap W).comp (map φ hf Z W h) := by
  apply hom_ext
  intro M
  simp only [AddMonoidHom.comp_apply, resolutionMap_mk, map_mk]
  exact resClass_map φ hf Z W h M
end G0WithSupport

namespace K0WithSupport
lemma homologyEuler_enlarge {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)} (h : Z ≤ W) :
    (homologyEuler W).comp (enlarge h) = (G0WithSupport.enlarge h).comp (homologyEuler Z) := by
  have hres := G0WithSupport.resolutionMap_enlarge h
  have h := congrArg (fun f => ((homologyEuler W).comp f).comp (homologyEuler Z)) hres
  simp only [AddMonoidHom.comp_assoc, resolutionMap_homologyEuler, AddMonoidHom.comp_id] at h
  rw [← AddMonoidHom.comp_assoc, homologyEuler_resolutionMap, AddMonoidHom.id_comp] at h
  exact h

lemma homologyEuler_map (φ : R →+* S) (hf : φ.Flat)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W : TopologicalSpace.Closeds (PrimeSpectrum S)) (h : supportPullback φ Z ≤ W) :
    (homologyEuler W).comp (map φ Z W h) =
      (G0WithSupport.map φ hf Z W h).comp (homologyEuler Z) := by
  have hres := G0WithSupport.resolutionMap_map φ hf Z W h
  have hc := congrArg (fun f => ((homologyEuler W).comp f).comp (homologyEuler Z)) hres
  simp only [AddMonoidHom.comp_assoc, resolutionMap_homologyEuler, AddMonoidHom.comp_id] at hc
  rw [← AddMonoidHom.comp_assoc, homologyEuler_resolutionMap, AddMonoidHom.id_comp] at hc
  exact hc
end K0WithSupport
end SerrePositivity

end ComparisonNaturalityPart
