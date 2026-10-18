module

public import SerrePositivity.KST.DerivedBlowup.ExteriorIntegerInclusion

/-!
概要：KST Def3.1 の整数次数 Koszul 微分と総外積の収縮の対応を全次数で証明する。
方針：負次数の標準同型、次数0の収縮消滅、正次数の零対象性を合わせる。
規約：微分は q→q+1。使われ方：全双次数での Leibniz 則を chain 条件へ移す。
-/

@[expose] public noncomputable section

universe u v

namespace SerrePositivity.KST.DerivedBlowup

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- 概要：全整数次数で各項の包含は微分と収縮を交換する。
方針：負・零・正の三つの場合を既存の比較に帰着する。
規約：KST Def3.1。使われ方：Koszul 積の chain map 条件を総外積代数で検証する。 -/
theorem exteriorCochainInclusion_d (d : M →ₗ[R] R) (q : ℤ)
    (z : (exteriorKoszulCochain d).X q) :
    exteriorCochainInclusion d (q + 1) (((exteriorKoszulCochain d).d q (q + 1)).hom z) =
      CliffordAlgebra.contractLeft (Q := 0) d (exteriorCochainInclusion d q z) := by
  cases q with
  | ofNat n =>
    cases n with
    | zero =>
      have hc := exteriorContraction_zero_degree d (exteriorCochainInclusion d 0 z)
        (exteriorCochainInclusion_mem d 0 z)
      simpa [exteriorCochainInclusion] using hc.symm
    | succ n =>
      have := ModuleCat.subsingleton_of_isZero
        (exteriorKoszulCochain_isZero_X_pos d ((n + 1 : ℕ) : ℤ) (by omega))
      have hz : z = 0 := Subsingleton.elim _ _
      subst z
      simp only [map_zero]
  | negSucc n =>
    have hn : Int.negSucc n + 1 = -(n : ℤ) := by omega
    rw [hn]
    change exteriorCochainInclusion d (-(n : ℤ))
        (((exteriorKoszulCochain d).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))).hom z) =
      CliffordAlgebra.contractLeft (Q := 0) d
        (exteriorCochainInclusion d (-((n + 1 : ℕ) : ℤ)) z)
    rw [exteriorCochainInclusion_neg, exteriorCochainInclusion_neg]
    exact exteriorCochainInclusionNeg_d d n z

end SerrePositivity.KST.DerivedBlowup
