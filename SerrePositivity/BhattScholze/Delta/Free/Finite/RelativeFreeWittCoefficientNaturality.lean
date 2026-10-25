module

public import SerrePositivity.BhattScholze.Delta.Basic.DeltaWitt
public import SerrePositivity.BhattScholze.Delta.Free.Finite.RelativeFreeWittCoordinateChange

/-! # 基底係数のWitt像と逆座標射での固定

相対係数δ射の自然性を使い、基底Witt係数を直接比較する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 相対自由環の基底係数のWitt元は、基底Witt元の係数包含像。 -/
theorem deltaWittGhostVector_relativeFree_C (D : DeltaStructure p A)
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (a : A) :
    deltaWittGhostVector (relativeFreeDeltaStructure σ D) (MvPolynomial.C a) =
      WittVector.map MvPolynomial.C (deltaWittGhostVector D a) :=
  (deltaWittGhostVector_map D (relativeFreeDeltaStructure σ D) MvPolynomial.C
    (relativeFreeDeltaStructure_C_isDeltaHom σ D) hg a).symm

/-- 全基底Witt係数は相対自由環への通常係数像に一致する。 -/
theorem deltaWittGhostVector_relativeFree_C_coeff (D : DeltaStructure p A)
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (a : A) (n : ℕ) :
    (deltaWittGhostVector (relativeFreeDeltaStructure σ D) (MvPolynomial.C a)).coeff n =
      MvPolynomial.C ((deltaWittGhostVector D a).coeff n) := by
  rw [deltaWittGhostVector_relativeFree_C D hg, WittVector.map_coeff]

/-- 逆座標射は基底係数の全Witt係数を固定する。 -/
theorem relativeFreeWittInverseMap_coefficient_C (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (a : A) (n : ℕ) :
    relativeFreeWittInverseMap D hp
      ((deltaWittGhostVector (relativeFreeDeltaStructure σ D) (MvPolynomial.C a)).coeff n) =
        MvPolynomial.C ((deltaWittGhostVector D a).coeff n) := by
  rw [deltaWittGhostVector_relativeFree_C_coeff D hg]
  exact AlgHom.commutes (relativeFreeWittInverseMap D hp) _

/-- 逆座標係数射は基底係数のWitt元全体も固定する。 -/
theorem relativeFreeWittInverseMap_wittVector_C (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a))
    (hg : Function.Injective (WittVector.ghostMap :
      WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
    (a : A) :
    WittVector.map (relativeFreeWittInverseMap D hp).toRingHom
      (deltaWittGhostVector (relativeFreeDeltaStructure σ D) (MvPolynomial.C a)) =
        deltaWittGhostVector (relativeFreeDeltaStructure σ D) (MvPolynomial.C a) := by
  apply WittVector.ext
  intro n
  rw [WittVector.map_coeff]
  change relativeFreeWittInverseMap D hp
    ((deltaWittGhostVector (relativeFreeDeltaStructure σ D) (MvPolynomial.C a)).coeff n) = _
  rw [relativeFreeWittInverseMap_coefficient_C D hp hg,
    deltaWittGhostVector_relativeFree_C_coeff D hg]

end SerrePositivity.BhattScholze
