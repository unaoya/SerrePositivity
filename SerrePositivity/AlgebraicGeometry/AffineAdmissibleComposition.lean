module

public import SerrePositivity.AlgebraicGeometry.AffineCompositionDomination
public import SerrePositivity.AlgebraicGeometry.AdmissibleRefinement
public import SerrePositivity.AlgebraicGeometry.RestrictionOpenOrder

/-!
概要：KST §5、Stacks 080Y の Noether アフィン基底上の admissible blowup の合成支配。
方針：中心の降下等式と中心外同型から admissible 性を戻し、積中心の支配射を使う。
規約：二段目の中心は元の U の逆像を避けると仮定する。
使われ方：有限回の admissible blowup を一つで支配するアフィン段階。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory

/--
概要：中心イデアル層の正の冪を取っても中心外開集合は変わらない。
方針：正の冪の支持の公式を使う。
規約：KST §5、Stacks 080Y、指数は正。
使われ方：中心の降下の捻りの支持を取り除く。
-/
theorem centerComplement_pow {X : Scheme.{u}} (K : X.IdealSheafData)
    (n : ℕ) (hn : 0 < n) : centerComplement (K ^ n) = centerComplement K := by
  simp only [centerComplement, K.support_pow n hn.ne']

set_option backward.isDefEq.respectTransparency false in
/--
概要：アフィンの積中心の補開集合は両中心の補開集合の共通部分。
方針：積イデアルの零点集合の和の公式を使う。
規約：KST §5、Stacks 080Y、任意の二イデアル。
使われ方：合成を支配する積中心の admissible 性。
-/
theorem affineCenterComplement_mul {R : Type u} [CommRing R] (I J : Ideal R) :
    affineCenterComplement (I * J) = affineCenterComplement I ⊓ affineCenterComplement J := by
  ext x
  change (x : PrimeSpectrum R) ∈ affineCenterComplement (I * J) ↔
    x ∈ affineCenterComplement I ∧ x ∈ affineCenterComplement J
  have hmul : x ∈ PrimeSpectrum.zeroLocus (I * J : Set R) ↔
      x ∈ PrimeSpectrum.zeroLocus (I : Set R) ∨ x ∈ PrimeSpectrum.zeroLocus (J : Set R) := by
    rw [PrimeSpectrum.zeroLocus_mul]
    rfl
  exact (mem_affineCenterComplement (I * J) x).trans
    ((not_congr hmul).trans (not_or.trans
      ((mem_affineCenterComplement I x).symm.and (mem_affineCenterComplement J x).symm)))

variable {R : Type u} [CommRing R] (I J : Ideal R)
  (K : (affineBlowup I).IdealSheafData) (U : (Spec (.of R)).Opens)

set_option backward.isDefEq.respectTransparency false in
/--
概要：二段目の中心が U の逆像を避けるなら、正の冪で降下した基底中心も U を避ける。
方針：降下等式の支持を計算し、U 上の構造射の同型性で逆像の包含を基底へ戻す。
規約：KST §5、Stacks 080Y、降下次数 D は正。
使われ方：構成した中心を admissible blowup の中心として使う。
-/
theorem affine_center_descent_admissible (D : ℕ) (hD : 0 < D)
    (hI : U ≤ affineCenterComplement I)
    (hK : affineBlowupπ I ⁻¹ᵁ U ≤ centerComplement K)
    (hJ : ((specIdealEquiv (.of R)).symm J).comap (affineBlowupπ I) =
      affineExceptionalIdealSheaf I ^ D * K) : U ≤ affineCenterComplement J := by
  have := affineBlowupπ_restrict_complement_isIso I
  have := isIso_restrict_of_open_le (affineBlowupπ I) U (affineCenterComplement I) hI
  apply open_le_of_preimage_le_of_restrict_isIso (affineBlowupπ I) U (affineCenterComplement J)
  have hCJ : affineBlowupπ I ⁻¹ᵁ affineCenterComplement J =
      centerComplement (((specIdealEquiv (.of R)).symm J).comap (affineBlowupπ I)) := by
    rw [← preimage_centerComplement_comap, centerComplement_specIdealEquiv,
      OrderIso.apply_symm_apply]
  have hCE : centerComplement (affineExceptionalIdealSheaf I) =
      affineBlowupπ I ⁻¹ᵁ affineCenterComplement I := by
    rw [affineExceptionalIdealSheaf, ← preimage_centerComplement_comap,
      centerComplement_specIdealEquiv, OrderIso.apply_symm_apply]
  rw [hCJ, hJ, centerComplement_mul, centerComplement_pow _ D hD, hCE]
  exact le_inf (fun x hx => hI hx) hK

/--
概要：Noether アフィン基底上の二段の U-admissible blowup は一つの U-admissible blowup で支配される。
方針：正の降下次数を選び、降下中心の admissible 性と積中心による実際の支配射を使う。
規約：KST §5、Stacks 080Y、支配は元の基底への可換な因子化。
使われ方：admissible blowup の合成の支配のアフィン基底版。
-/
theorem exists_affine_admissible_composition_domination [IsNoetherianRing R]
    (hI : U ≤ affineCenterComplement I)
    (hK : affineBlowupπ I ⁻¹ᵁ U ≤ centerComplement K) :
    ∃ L : Ideal R, L.FG ∧ U ≤ affineCenterComplement L ∧
      ∃ g : affineBlowup L ⟶ blowup K,
        g ≫ blowupπ K ≫ affineBlowupπ I = affineBlowupπ L := by
  obtain ⟨N, hN⟩ := exists_affine_center_descent I K
  obtain ⟨J, _, _, hJ⟩ := hN (N + 1) (Nat.le_succ N)
  have hJU := affine_center_descent_admissible I J K U (N + 1) (Nat.succ_pos N) hI hK hJ
  have hchart (a : I) : J.map (chartBaseMap I a) =
      Ideal.span {chartBaseMap I a a.1 ^ (N + 1)} * blowupChartIdeal I K a := by
    rw [← blowupChartIdeal_base_comap I J a, hJ, blowupChartIdeal_mul, blowupChartIdeal_pow,
      affineExceptionalIdealSheaf_chart, Ideal.span_singleton_pow]
  obtain ⟨g, hg⟩ := exists_affine_composition_lift_of_descent I J K (N + 1) hchart
  refine ⟨I * J, Ideal.fg_of_isNoetherianRing _, ?_, g, ?_⟩
  · rw [affineCenterComplement_mul]
    exact le_inf hI hJU
  · rw [← Category.assoc, hg, affineBlowupProductLeftMap_base]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
