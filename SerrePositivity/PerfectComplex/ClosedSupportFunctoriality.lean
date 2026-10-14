module

public import SerrePositivity.PerfectComplex.ClosedSupportComparison
public import SerrePositivity.PerfectComplex.BaseChange

/-! # 閉集合版 K₀ の台の拡大と基底変更

有限射影複体の台は任意の環準同型による逆像へ移る。
生成イデアルの有限生成性や基底変更の平坦性を要求しない。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity

open CategoryTheory Limits Pretriangulated

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- Pull back a closed support along the map of prime spectra. -/
def supportPullback (φ : R →+* S) (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) :
    TopologicalSpace.Closeds (PrimeSpectrum S) :=
  ⟨(PrimeSpectrum.comap φ) ⁻¹' Z, Z.isClosed.preimage (PrimeSpectrum.continuous_comap φ)⟩

@[simp] lemma mem_supportPullback (φ : R →+* S)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (p : PrimeSpectrum S) :
    p ∈ supportPullback φ Z ↔ PrimeSpectrum.comap φ p ∈ Z := Iff.rfl

@[simp] lemma supportPullback_id (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) :
    supportPullback (RingHom.id R) Z = Z := by
  ext p
  simp [supportPullback, PrimeSpectrum.comap_id]

@[simp] lemma supportPullback_comp (φ : R →+* S) (ψ : S →+* T)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) :
    supportPullback ψ (supportPullback φ Z) = supportPullback (ψ.comp φ) Z := by
  ext p
  simp [supportPullback]

lemma supportPullback_mono (φ : R →+* S)
    {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)} (h : Z ≤ W) :
    supportPullback φ Z ≤ supportPullback φ W := by
  intro p hp
  exact h hp

@[simp] lemma supportPullback_zeroLocus (φ : R →+* S) (I : Ideal R) :
    supportPullback φ (supportZeroLocus I) = supportZeroLocus (I.map φ) := by
  ext p
  change I ≤ p.asIdeal.comap φ ↔ I.map φ ≤ p.asIdeal
  exact Ideal.map_le_iff_le_comap.symm

/-- Geometric support of a bounded finite-projective complex pulls back under any ring map. -/
lemma HasHomologySupportOn.baseChange (φ : R →+* S)
    {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (hs : HasHomologySupportOn Z P)
    (hp : strictlyPerfectComplex R P) :
    HasHomologySupportOn (supportPullback φ Z) (baseChange φ P) := by
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp Z.isClosed
  intro i p hmem
  change PrimeSpectrum.comap φ p ∈ (Z : Set (PrimeSpectrum R))
  rw [hI]
  intro r hr
  let w : Fin 1 → R := fun _ ↦ r
  have hsingle : HasHomologySupport (Ideal.span (Set.range w)) P := by
    intro q t ht a ha
    have hit : t ∈ PrimeSpectrum.zeroLocus (I : Set R) := by
      rw [← hI]
      exact hs q ht
    apply Ideal.span_le.mpr ?_ ha
    rintro _ ⟨j, rfl⟩
    exact hit hr
  have hbound : ∃ a b : ℤ, ∀ q, (q < a ∨ b < q) → IsZero (P.X q) := by
    obtain ⟨a, b, ha, hb⟩ := hp.1
    exact ⟨a, b, fun q h ↦ h.elim (fun h ↦ P.isZero_of_isStrictlyGE a q h)
      (fun h ↦ P.isZero_of_isStrictlyLE b q h)⟩
  have hproj (q : ℤ) : Projective (P.X q) := by
    have := (hp.2 q).2
    infer_instance
  have hscalar := isSupported_of_homologySupport w P (fun q ↦ (hp.2 q).1) hproj
    hbound hsingle
  have hb := (isSupported_baseChange φ hscalar).homologySupport i hmem
  exact hb (Ideal.subset_span (Set.mem_range_self (0 : Fin 1)))

/-- Ring change preserves the closed support property in the perfect homotopy category. -/
lemma perfectChangeRing_supportedOn (φ : R →+* S)
    {Z : TopologicalSpace.Closeds (PrimeSpectrum R)} (X : PerfectHomotopy R)
    (hs : perfectHomotopySupportedOn Z X) :
    perfectHomotopySupportedOn (supportPullback φ Z) ((perfectChangeRing φ).obj X) := by
  obtain ⟨X, hp⟩ := X
  obtain ⟨P : CochainComplex _ _, rfl⟩ := X.quotient_obj_surjective
  have hP := (perfectHomotopyProperty_quotient R P).mp hp
  exact (perfectHomotopyObj_supportedOn_iff _ (baseChange φ P)
    (strictlyPerfectComplex_baseChange φ P hP)).mpr
      (((perfectHomotopyObj_supportedOn_iff Z P hP).mp hs).baseChange φ hP)

variable {Z W V : TopologicalSpace.Closeds (PrimeSpectrum R)}

/-- The inclusion induced by enlarging support. -/
def closedSupportEnlarge (h : Z ≤ W) : SupportedPerfectHomotopyOn Z ⥤
    SupportedPerfectHomotopyOn W :=
  (perfectHomotopySupportedOn W).lift (supportedPerfectOnInclusion Z)
    (fun X i ↦ (X.property i).trans h)

instance (h : Z ≤ W) : (closedSupportEnlarge h).CommShift ℤ := by
  exact ObjectProperty.commShiftLift (perfectHomotopySupportedOn W)
    (supportedPerfectOnInclusion Z) _

instance (h : Z ≤ W) : (closedSupportEnlarge h).IsTriangulated := by
  exact ObjectProperty.isTriangulated_lift (perfectHomotopySupportedOn W)
    (supportedPerfectOnInclusion Z) _

/-- Change rings and then, optionally, enlarge the inverse-image support. -/
def closedSupportChangeRing (φ : R →+* S) (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W : TopologicalSpace.Closeds (PrimeSpectrum S)) (h : supportPullback φ Z ≤ W) :
    SupportedPerfectHomotopyOn Z ⥤ SupportedPerfectHomotopyOn W :=
  (perfectHomotopySupportedOn W).lift (supportedPerfectOnInclusion Z ⋙ perfectChangeRing φ)
    (fun X i ↦ (perfectChangeRing_supportedOn φ X.obj X.property i).trans h)

instance (φ : R →+* S) (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W : TopologicalSpace.Closeds (PrimeSpectrum S)) (h : supportPullback φ Z ≤ W) :
    (closedSupportChangeRing φ Z W h).CommShift ℤ := by
  exact ObjectProperty.commShiftLift (perfectHomotopySupportedOn W)
    (supportedPerfectOnInclusion Z ⋙ perfectChangeRing φ) _

instance (φ : R →+* S) (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W : TopologicalSpace.Closeds (PrimeSpectrum S)) (h : supportPullback φ Z ≤ W) :
    (closedSupportChangeRing φ Z W h).IsTriangulated := by
  exact ObjectProperty.isTriangulated_lift (perfectHomotopySupportedOn W)
    (supportedPerfectOnInclusion Z ⋙ perfectChangeRing φ) _

namespace K0WithSupport

/-- Enlarge support on Grothendieck groups. -/
def enlarge (h : Z ≤ W) : K0WithSupport Z →+ K0WithSupport W :=
  TriangulatedK0.map (closedSupportEnlarge h)

@[simp] lemma enlarge_mk (h : Z ≤ W) (X : SupportedPerfectHomotopyOn Z) :
    enlarge h (mk Z X) = mk W ((closedSupportEnlarge h).obj X) := TriangulatedK0.map_mk ..

@[simp] lemma enlarge_refl : enlarge (le_refl Z) = AddMonoidHom.id _ := by
  apply hom_ext
  intro X
  simp only [enlarge_mk, AddMonoidHom.id_apply]
  exact TriangulatedK0.mk_iso (ObjectProperty.isoMk _ (Iso.refl _))

lemma enlarge_comp (hZW : Z ≤ W) (hWV : W ≤ V) :
    (enlarge hWV).comp (enlarge hZW) = enlarge (hZW.trans hWV) := by
  apply hom_ext
  intro X
  simp only [AddMonoidHom.comp_apply, enlarge_mk]
  exact TriangulatedK0.mk_iso (ObjectProperty.isoMk _ (Iso.refl _))

/-- Ring change on Grothendieck groups, allowing a larger target support. -/
def map (φ : R →+* S) (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W : TopologicalSpace.Closeds (PrimeSpectrum S)) (h : supportPullback φ Z ≤ W) :
    K0WithSupport Z →+ K0WithSupport W := TriangulatedK0.map (closedSupportChangeRing φ Z W h)

@[simp] lemma map_mk (φ : R →+* S) (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W : TopologicalSpace.Closeds (PrimeSpectrum S)) (h : supportPullback φ Z ≤ W)
    (X : SupportedPerfectHomotopyOn Z) :
    map φ Z W h (mk Z X) = mk W ((closedSupportChangeRing φ Z W h).obj X) :=
  TriangulatedK0.map_mk ..

lemma map_comp (φ : R →+* S) (ψ : S →+* T)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W : TopologicalSpace.Closeds (PrimeSpectrum S))
    (V : TopologicalSpace.Closeds (PrimeSpectrum T))
    (hφ : supportPullback φ Z ≤ W) (hψ : supportPullback ψ W ≤ V)
    (hcomp : supportPullback (ψ.comp φ) Z ≤ V) :
    (map ψ W V hψ).comp (map φ Z W hφ) = map (ψ.comp φ) Z V hcomp := by
  apply hom_ext
  intro X
  simp only [AddMonoidHom.comp_apply, map_mk]
  exact TriangulatedK0.mk_iso
    (ObjectProperty.isoMk _ ((perfectChangeRingCompIso φ ψ).app X.obj))

lemma map_id (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (h : supportPullback (RingHom.id R) Z ≤ Z) :
    map (RingHom.id R) Z Z h = AddMonoidHom.id _ := by
  apply hom_ext
  intro X
  simp only [map_mk, AddMonoidHom.id_apply]
  let P := X.obj.obj.as
  let e : baseChange (RingHom.id R) P ≅ P :=
    (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsId R) (.up ℤ)).app P ≪≫
      (Functor.mapHomologicalComplexIdIso (ModuleCat.{u} R) (.up ℤ)).app P
  exact TriangulatedK0.mk_iso
    (ObjectProperty.isoMk _ (ObjectProperty.isoMk _ ((homotopyQuot R).mapIso e)))

lemma enlarge_map (φ : R →+* S)
    (Z Z' : TopologicalSpace.Closeds (PrimeSpectrum R))
    (W W' : TopologicalSpace.Closeds (PrimeSpectrum S)) (hZZ' : Z ≤ Z') (hWW' : W ≤ W')
    (hφ : supportPullback φ Z ≤ W) (hφ' : supportPullback φ Z' ≤ W') :
    (enlarge hWW').comp (map φ Z W hφ) = (map φ Z' W' hφ').comp (enlarge hZZ') := by
  apply hom_ext
  intro X
  simp only [AddMonoidHom.comp_apply, map_mk, enlarge_mk]
  exact TriangulatedK0.mk_iso (ObjectProperty.isoMk _ (Iso.refl _))

end K0WithSupport

/-- Pullback of a support specified by a generating list. -/
lemma supportPullback_span (φ : R →+* S) {e : ℕ} (z : Fin e → R) :
    supportPullback φ (supportZeroLocus (Ideal.span (Set.range z))) =
      supportZeroLocus (Ideal.span (Set.range (φ ∘ z))) := by
  rw [supportPullback_zeroLocus, Ideal.map_span, ← Set.range_comp]

/-- The new base-change map agrees with the existing map on finite-free classes. -/
lemma freeToClosedSupportK0_map (φ : R →+* S) {e : ℕ} (z : Fin e → R) :
    (K0WithSupport.map φ (supportZeroLocus (Ideal.span (Set.range z)))
      (supportZeroLocus (Ideal.span (Set.range (φ ∘ z))))
      (le_of_eq (supportPullback_span φ z))).comp (freeToClosedSupportK0 z) =
    (freeToClosedSupportK0 (φ ∘ z)).comp (K0.map φ) := by
  apply K0.hom_ext
  intro P
  simp only [AddMonoidHom.comp_apply, freeToClosedSupportK0_mk, K0WithSupport.map_mk,
    K0.map_mk]
  exact TriangulatedK0.mk_iso (ObjectProperty.isoMk _ (ObjectProperty.isoMk _ (Iso.refl _)))

end SerrePositivity
