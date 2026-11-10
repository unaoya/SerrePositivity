module

public import SerrePositivity.AlgebraicGeometry.IdealComplementPullback
public import SerrePositivity.AlgebraicGeometry.LocalFlatPureRefinement
public import SerrePositivity.AlgebraicGeometry.PureTransformRestrictBase

/-!
概要：基底の有限個の主開で得た平坦化中心を、一つのアフィン基底中心にまとめる。
方針：局所中心を既存の大域的な共通細分へ渡し、元の環上の中心に戻す。
規約：境界は基底の一つの主開で表す。
使われ方：Stacks 0815 で各自由化主開が基底を覆うよう縮めた後、局所中心を貼り合わせる。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
/--
概要：単位イデアルを生成する元による各基底局所化で純変換を平坦化できれば、基底全体で平坦化できる。
方針：各主開の局所中心をアフィン開被覆の中心としてまとめ、その blowup に沿う平坦性を移す。
規約：中心はすべて境界外で自明とする。
使われ方：余核の帰納で得た基底主開上の中心の大域化。
-/
theorem exists_affine_flatPure_center_of_basicOpen_centers
    {R : Type u} [CommRing R] [IsNoetherianRing R] {ι : Type v} [Finite ι]
    (s : ι → R) (hs : Ideal.span (Set.range s) = ⊤)
    (a : R) (M : Type w) [AddCommGroup M] [Module R M]
    (J : ∀ i, Ideal (Localization.Away (s i)))
    (hJ : ∀ i, PrimeSpectrum.basicOpen (algebraMap R (Localization.Away (s i)) a) ≤
      affineCenterComplement (J i))
    (hflat : ∀ i, let L := CommRingCat.of (Localization.Away (s i))
      letI : Algebra (CommRingCat.of R) L := inferInstanceAs (Algebra R (Localization.Away (s i)))
      HasFlatPurePullbacks (affineBlowupπ (J i)) (algebraMap (CommRingCat.of R) L a)
        (L ⊗[CommRingCat.of R] M)) :
    ∃ I : Ideal R, I.FG ∧ PrimeSpectrum.basicOpen a ≤ affineCenterComplement I ∧
      HasFlatPurePullbacks (affineBlowupπ I) a M := by
  let A := CommRingCat.of R
  let S := Spec A
  let U : S.Opens := PrimeSpectrum.basicOpen a
  let 𝒰 := Scheme.affineOpenCoverOfSpanRangeEqTop (R := A) s hs
  let : Finite 𝒰.I₀ := inferInstanceAs (Finite ι)
  let L (i : 𝒰.I₀) := (specIdealEquiv (𝒰.X i)).symm (J i)
  have hL (i : 𝒰.I₀) : IsUAdmissibleCenter (𝒰.f i ⁻¹ᵁ U) (L i) := by
    change _ ≤ centerComplement (L i)
    rw [Scheme.affineOpenCoverOfSpanRangeEqTop_f, SpecMap_preimage_basicOpen,
      centerComplement_specIdealEquiv, show specIdealEquiv (𝒰.X i) (L i) = J i from
      (specIdealEquiv (𝒰.X i)).apply_symm_apply _]
    exact hJ i
  have hLflat (i : 𝒰.I₀) : HasFlatPurePullbacks
      (affineBlowupπ (specIdealEquiv (𝒰.X i) (L i)) ≫ 𝒰.f i ≫ 𝟙 S) a M := by
    let T := CommRingCat.of (Localization.Away (s i))
    let : Algebra A T := inferInstanceAs (Algebra R (Localization.Away (s i)))
    let φ : A ⟶ T := CommRingCat.ofHom (algebraMap A T)
    rw [Category.comp_id, show specIdealEquiv (𝒰.X i) (L i) = J i from
      (specIdealEquiv (𝒰.X i)).apply_symm_apply _]
    change HasFlatPurePullbacks (affineBlowupπ (J i) ≫ Spec.map φ) a M
    apply HasFlatPurePullbacks.restrictBase φ (affineBlowupπ (J i)) a M
    rw [show φ.hom = algebraMap A T from rfl, toAlgebra_algebraMap]
    exact hflat i
  obtain ⟨K, hKU, _, hKflat⟩ :=
    exists_admissible_flatPure_refinement (𝟙 S) a M U 𝒰 L hL hLflat
  let I := specIdealEquiv A (K.comap (𝟙 S))
  have hcenter : affineCenterComplement I = U := by
    change affineCenterComplement (specIdealEquiv A (K.comap (𝟙 S))) = U
    rw [← centerComplement_specIdealEquiv, Scheme.IdealSheafData.comap_id]
    exact hKU
  have hπ : blowupAffineOpenMap (𝟙 S) K ≫ (blowupπ K ≫ 𝟙 S) = affineBlowupπ I := by
    rw [Category.comp_id, blowupAffineOpenMap_base, Category.comp_id]
  exact ⟨I, IsNoetherian.noetherian _, hcenter.ge, hπ ▸ hKflat.comp (blowupAffineOpenMap (𝟙 S) K)⟩

end SerrePositivity.AlgebraicGeometry
