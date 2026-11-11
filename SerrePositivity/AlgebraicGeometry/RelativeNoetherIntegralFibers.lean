module

public import SerrePositivity.AlgebraicGeometry.EtaleAffineNormalizationRefinement
public import SerrePositivity.AlgebraicGeometry.RelativeNoetherRationalResidue

/-!
概要：指定点の相対 Noether 正規化を幾何学的整なファイバーを持つ形で実現する。
方針：次元と剰余体を制御した有限化に、指定ファイバーの幾何学的整な開への拡張を適用する。
規約：Noether なアフィン基底上の有限型アフィン始域を扱う。
使われ方：Stacks 057S から 0815 の滑らかな正規化先への還元。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

/--
概要：指定ファイバー点の近くで、元のファイバー成分の次元上限以下の滑らかな幾何学的整の族に有限写像を作れる。
方針：同じ正規化写像で次元と剰余体を制御し、その点を残して有限化したチャートを縮める。
規約：始域と基底の比較は étale、正規化先はアフィンとする。
使われ方：Stacks 057S のアフィンの場合を、余核による次元帰納へ渡す。
-/
theorem exists_dim_le_etale_finite_geometricallyIntegral_refinement
    {R B : Type u} [CommRing R] [IsNoetherianRing R] [CommRing B] [Algebra R B]
    [Algebra.FiniteType R B] (p : PrimeSpectrum R) (z : PrimeSpectrum (p.asIdeal.Fiber B))
    (d : WithBot ℕ∞)
    (hd : ∀ m ∈ minimalPrimes (p.asIdeal.Fiber B), m ≤ z.asIdeal →
      ringKrullDim ((p.asIdeal.Fiber B) ⧸ m) ≤ d) :
    ∃ (n : ℕ) (_ : (n : WithBot ℕ∞) ≤ d)
      (S' Y' X' : Scheme.{u}) (_ : IsAffine S') (_ : IsAffine Y') (_ : IsAffine X')
      (e : S' ⟶ Spec (.of R)) (j : X' ⟶ Spec (.of B)) (f' : Y' ⟶ S') (h' : X' ⟶ Y') (x' : X'),
      Etale e ∧ Etale j ∧
      j x' = z.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] p.asIdeal.Fiber B).toRingHom ∧
      h' ≫ f' ≫ e = j ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) ∧
      IsFinite h' ∧ SmoothOfRelativeDimension n f' ∧ GeometricallyIntegral f' := by
  obtain ⟨a, _, n, b, r, _, hn, x, hx, hxz, T, _, _, _, y, hy, _, e₀, _, w, hw, _, hwx, hwe,
    ⟨hres⟩, hfin, hsm, _⟩ :=
    exists_dim_le_etale_finite_piece_with_rational_residue p.asIdeal z.asIdeal d hd
  let P := MvPolynomial (Fin n) R
  let L := Localization.Away a
  let φ : P →ₐ[R] L := MvPolynomial.aeval b
  let : Algebra P L := φ.toRingHom.toAlgebra
  let : Algebra R T := ((algebraMap P T).comp (algebraMap R P)).toAlgebra
  let : IsScalarTower R P T := IsScalarTower.of_algebraMap_eq' rfl
  let D := T ⊗[P] L
  let C := Localization.Away e₀
  let uB := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let uT := Spec.map (CommRingCat.ofHom (algebraMap R T))
  let uP := Spec.map (CommRingCat.ofHom (algebraMap R P))
  let τ := Spec.map (CommRingCat.ofHom (algebraMap P T))
  let ψ := Spec.map (CommRingCat.ofHom φ.toRingHom)
  let l := Spec.map (CommRingCat.ofHom (algebraMap B L))
  let g := Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : L →ₐ[P] D).toRingHom)
  let fD := Spec.map (CommRingCat.ofHom (algebraMap T D))
  let o := Spec.map (CommRingCat.ofHom (algebraMap D C))
  let h := Spec.map (CommRingCat.ofHom (algebraMap T C))
  let qC := o ≫ g ≫ l
  have hP : IsPullback g fD ψ τ := isPullback_specTensor P L T
  have hτ : τ ≫ uP = uT := by
    rw [← Spec.map_comp]
    rfl
  have hψ : ψ ≫ uP = l ≫ uB := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext φ.commutes)
  have ho : o ≫ fD = h := by
    rw [← Spec.map_comp]
    rfl
  have hComm : h ≫ uT = qC ≫ uB := by
    rw [← ho, ← hτ, Category.assoc, ← Category.assoc fD, ← hP.w, Category.assoc, hψ]
    simp [qC, Category.assoc]
  let : Etale τ := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr inferInstance)
  let : Etale g := MorphismProperty.of_isPullback hP.flip (inferInstance : Etale τ)
  let : IsOpenImmersion l := IsOpenImmersion.of_isLocalization a
  let : IsOpenImmersion o := IsOpenImmersion.of_isLocalization e₀
  let : Etale qC := inferInstanceAs (Etale (o ≫ g ≫ l))
  let : IsFinite h := (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr hfin)
  let : SmoothOfRelativeDimension n uT := hsm
  let iso := IsLocalization.primeSpectrumOrderIso (.powers e₀) C
  let wD : {q : PrimeSpectrum D // Disjoint (Submonoid.powers e₀ : Set D) q.asIdeal} :=
    ⟨⟨w, hw⟩, (Ideal.disjoint_powers_iff_notMem_of_isPrime e₀).mpr hwe⟩
  let wC : Spec (.of C) := iso.symm wD
  have hwC : o wC = wD.1 := congrArg Subtype.val (iso.apply_symm_apply wD)
  let yT : PrimeSpectrum T := ⟨y, hy⟩
  let zB := z.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] p.asIdeal.Fiber B).toRingHom
  have hCz : qC wC = zB := by
    change l (g (o wC)) = zB
    rw [hwC, show g wD.1 = (⟨x, hx⟩ : PrimeSpectrum L) from PrimeSpectrum.ext hwx]
    exact PrimeSpectrum.ext hxz
  have hCy : h wC = yT := by
    rw [← ho]
    change fD (o wC) = yT
    rw [hwC]
    exact PrimeSpectrum.ext (w.over_def y).symm
  have hzp : uB zB = p := ((PrimeSpectrum.preimageHomeomorphFiber R B p).symm z).2
  have hCp : (h ≫ uT) wC = p := by
    rw [hComm]
    change uB (qC wC) = p
    rw [hCz, hzp]
  have hyp : uT yT = p := by
    change uT (h wC) = p at hCp
    simpa only [hCy] using hCp
  let : y.LiesOver p.asIdeal := ⟨(congrArg PrimeSpectrum.asIdeal hyp).symm⟩
  let k := p.asIdeal.ResidueField
  let P₀ := MvPolynomial (Fin r) k
  let F := FractionRing P₀
  let : IsScalarTower R k F := .to₁₂₄ R k P₀ F
  obtain ⟨v, hv⟩ := exists_fiber_evaluation_of_residueField_equiv p.asIdeal y hres
  have hv' : RingHom.ker (v.toRingHom.comp
      (Algebra.TensorProduct.includeRight : T →ₐ[R] p.asIdeal.Fiber T).toRingHom) =
      (h wC).asIdeal :=
    hv.trans (congrArg PrimeSpectrum.asIdeal hCy).symm
  let ι := ULift.{u} (Fin r)
  let eP : P₀ ≃ₐ[k] MvPolynomial ι k := MvPolynomial.renameEquiv k
    (Equiv.ulift.symm : Fin r ≃ ι)
  let eF : F ≃ₐ[k] FractionRing (MvPolynomial ι k) := IsFractionRing.algEquivOfAlgEquiv eP
  let v' := eF.toAlgHom.comp v
  have hv'' : RingHom.ker (v'.toRingHom.comp
      (Algebra.TensorProduct.includeRight : T →ₐ[R] p.asIdeal.Fiber T).toRingHom) =
      (h wC).asIdeal := by
    change RingHom.ker ((eF.toRingHom.comp v.toRingHom).comp _) = _
    rw [RingHom.comp_assoc]
    exact (RingHom.ker_comp_of_injective (f := eF.toRingHom) _ eF.injective).trans hv'
  obtain ⟨S', Y', X', hS', hY', hX', e, j, f', h', x', he, hj, hx', hc, hfin', hsm', hgi⟩ :=
    exists_etale_affine_finite_refinement_of_rational_fiber_point
      (B := T) (ι := ι) (n := n) h wC p hCp v' hv''
  refine ⟨n, hn, S', Y', X', hS', hY', hX', e, j ≫ qC, f', h', x', he,
    inferInstance, ?_, ?_, hfin', hsm', hgi⟩
  · rw [Scheme.Hom.comp_apply, hx', hCz]
  · rw [hc, Category.assoc, hComm]

end SerrePositivity.AlgebraicGeometry
