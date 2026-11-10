module

public import SerrePositivity.AlgebraicGeometry.EtaleRationalFiberIntegralOpen
public import SerrePositivity.AlgebraicGeometry.GeometricIntegralAffineNeighborhood
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
概要：純超越な剰余体の点を持つ相対正規化先を、幾何学的整な滑らかなアフィン族へ縮める。
方針：基底を初等 étale 近傍へ移し、有限写像を選んだファイバー成分の開近傍に引き戻す。
規約：最初の有限写像と正規化先の相対次元は入力とする。
使われ方：Stacks 057S の次元と剰余体を制御する相対正規化から 0815 へ進む。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

/--
概要：滑らかな正規化先に純超越な体値点があれば、有限写像を保ったまま幾何学的整な族に縮められる。
方針：指定成分の幾何学的整な開を取り、元の指定点の持ち上げを含むアフィン開へ制限する。
規約：滑らかな正規化先は多項式環上 étale とし、相対次元は縮小で保つ。
使われ方：Stacks 057S の有限写像を、0815 が使う幾何学的整なアフィン族にする。
-/
theorem exists_etale_affine_finite_refinement_of_rational_fiber_point
    {R B ι : Type u} [CommRing R] [IsNoetherianRing R] [CommRing B] [Algebra R B] [Finite ι]
    {n : ℕ} [Algebra (MvPolynomial (Fin n) R) B] [IsScalarTower R (MvPolynomial (Fin n) R) B]
    [Algebra.Etale (MvPolynomial (Fin n) R) B]
    [SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap R B)))]
    {X : Scheme.{u}} (h : X ⟶ Spec (.of B)) [IsFinite h] (x : X) (p : PrimeSpectrum R)
    (hp : (h ≫ Spec.map (CommRingCat.ofHom (algebraMap R B))) x = p)
    (y : p.asIdeal.Fiber B →ₐ[p.asIdeal.ResidueField]
      FractionRing (MvPolynomial ι p.asIdeal.ResidueField))
    (hy : RingHom.ker (y.toRingHom.comp
      (Algebra.TensorProduct.includeRight : B →ₐ[R] p.asIdeal.Fiber B).toRingHom) = (h x).asIdeal) :
    ∃ (S' Y' X' : Scheme.{u}) (_ : IsAffine S') (_ : IsAffine Y') (_ : IsAffine X')
      (e : S' ⟶ Spec (.of R)) (j : X' ⟶ X) (f' : Y' ⟶ S') (h' : X' ⟶ Y') (x' : X'),
      Etale e ∧ Etale j ∧ j x' = x ∧
      h' ≫ f' ≫ e = j ≫ h ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) ∧
      IsFinite h' ∧ SmoothOfRelativeDimension n f' ∧ GeometricallyIntegral f' := by
  obtain ⟨b, hb, T, _, _, _, s, _, _, U, V, hU, _, _, hV, hVU, hInt⟩ :=
    exists_etale_geometricallyIntegral_open_of_rational_fiber_point (n := n) p y
  let L := Localization.Away b
  let E := T ⊗[R] L
  let u := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let uL := Spec.map (CommRingCat.ofHom (algebraMap R L))
  let l := Spec.map (CommRingCat.ofHom (algebraMap B L))
  let g := Spec.map (CommRingCat.ofHom (algebraMap R T))
  let a := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : L →ₐ[R] E).toRingHom)
  let f := Spec.map (CommRingCat.ofHom (algebraMap T E))
  let i := a ≫ l
  have hl : l ≫ u = uL := by
    rw [← Spec.map_comp]
    rfl
  have hPb : IsPullback a f uL g := isPullback_specTensor R L T
  have hbase : f ≫ g = i ≫ u := by
    rw [hPb.w.symm, Category.assoc, hl]
  let : IsOpenImmersion l := IsOpenImmersion.of_isLocalization b
  let : Etale g := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr inferInstance)
  let : Etale a := MorphismProperty.of_isPullback hPb.flip (inferInstance : Etale g)
  let : Etale i := inferInstanceAs (Etale (a ≫ l))
  have hbu : h x ∈ Set.range l := by
    rw [show Set.range l = (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B)) from
      PrimeSpectrum.localization_away_comap_range L b]
    intro hmem
    apply hb
    have hbker : b ∈ RingHom.ker (y.toRingHom.comp
        (Algebra.TensorProduct.includeRight : B →ₐ[R] p.asIdeal.Fiber B).toRingHom) := by
      rw [hy]
      exact hmem
    exact RingHom.mem_ker.mp hbker
  obtain ⟨v, hv⟩ := hbu
  have hvs : uL v = g s := by
    rw [← hl, Scheme.Hom.comp_apply, hv, ← Scheme.Hom.comp_apply, hp]
    exact (PrimeSpectrum.ext (s.asIdeal.over_def p.asIdeal).symm : g s = p).symm
  obtain ⟨w, hwv, hws⟩ := Scheme.exists_preimage_of_isPullback hPb v s hvs
  have hw : h x = i w := by rw [Scheme.Hom.comp_apply, hwv, hv]
  obtain ⟨z, hzx, hzw⟩ := Scheme.Pullback.exists_preimage_pullback x w hw
  let k := pullback.snd h i
  have hzV : k z ∈ V := hV (by
    change f (k z) = s
    rw [show k z = w from hzw]
    exact hws)
  let zV : k ⁻¹ᵁ V := ⟨z, hzV⟩
  let jV := (k ⁻¹ᵁ V).ι
  let fV := (Spec (.of E)).homOfLE hVU ≫ f ∣_ U
  have hfV : fV ≫ U.ι = V.ι ≫ f := by
    unfold fV
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, (Spec (.of E)).homOfLE_ι hVU]
  let : SmoothOfRelativeDimension n uL := hl ▸ (by
    simpa only [zero_add] using (inferInstance : SmoothOfRelativeDimension (0 + n) (l ≫ u)))
  let : SmoothOfRelativeDimension n f :=
    MorphismProperty.of_isPullback hPb (inferInstance : SmoothOfRelativeDimension n uL)
  let : SmoothOfRelativeDimension n (f ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f U).flip
      (inferInstance : SmoothOfRelativeDimension n f)
  let : SmoothOfRelativeDimension n fV := by
    simpa only [zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + n) ((Spec (.of E)).homOfLE hVU ≫ f ∣_ U))
  let : IsAffine (U : Scheme) := hU
  let : GeometricallyIntegral fV := hInt
  let : IsFinite (k ∣_ V) := inferInstanceAs (IsFinite ((pullback.snd h i) ∣_ V))
  obtain ⟨S', Y', X', hS', hY', hX', jS, jY, jX, f', h', x', hJS, hJY, hF, hP,
    hX, hfin, hsm, hgi⟩ :=
    exists_affine_finite_refinement_of_geometricallyIntegral_smooth (k ∣_ V) fV (n := n) zV
  let e := jS ≫ U.ι ≫ g
  let j := jX ≫ jV ≫ pullback.fst h i
  let : IsOpenImmersion jX := MorphismProperty.of_isPullback hP.flip hJY
  let : Etale (pullback.fst h i) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback h i).flip (inferInstance : Etale i)
  refine ⟨S', Y', X', hS', hY', hX', e, j, f', h', x', inferInstance, inferInstance, ?_, ?_,
    hfin, hsm, hgi⟩
  · change (pullback.fst h i) (jV (jX x')) = x
    rw [hX]
    exact hzx
  · simp only [e, j, Category.assoc]
    rw [reassoc_of% hF, ← reassoc_of% hP.w, reassoc_of% hfV, morphismRestrict_ι_assoc,
      hbase, ← pullback.condition_assoc]

end SerrePositivity.AlgebraicGeometry
