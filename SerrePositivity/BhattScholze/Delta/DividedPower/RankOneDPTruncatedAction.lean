module

public import SerrePositivity.BhattScholze.Delta.DividedPower.RankOneDPPrimeBlockBasis
public import Mathlib.RingTheory.AdjoinRoot

/-! # 実切断多項式環の作用と標準冪基底

既存AdjoinRootをそのまま使い、根を一次分冪生成元へ送る。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} {A : Type u} [CommRing A]
local notation "DA" => DividedPowerAlgebra A A
local notation "T₀" => AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)

/-- 根を一次分冪生成元へ送る、実切断多項式環からのA代数射。 -/
def rankOneDPTruncatedMap (hpos : 0 < p) (hp : (p : A) = 0) : T₀ →ₐ[A] DA :=
  AdjoinRoot.liftAlgHom ((Polynomial.X : Polynomial A) ^ p) (Algebra.ofId A DA)
    (DividedPowerAlgebra.dp A 1 (1 : A)) (by
      rw [Polynomial.eval₂_pow, Polynomial.eval₂_X]
      exact rankOneDPGenerator_pow_eq_zero hpos hp)

/-- 実作用射は、切断多項式環の根を指定された一次生成元へ送る。 -/
theorem rankOneDPTruncatedMap_root (hpos : 0 < p) (hp : (p : A) = 0) :
    rankOneDPTruncatedMap hpos hp (AdjoinRoot.root ((Polynomial.X : Polynomial A) ^ p)) =
      DividedPowerAlgebra.dp A 1 (1 : A) := by
  exact AdjoinRoot.lift_root (i := algebraMap A DA) (by
    rw [Polynomial.eval₂_pow, Polynomial.eval₂_X]
    exact rankOneDPGenerator_pow_eq_zero hpos hp)

/-- 上の実射による、切断多項式環の具体的スカラー作用。 -/
abbrev rankOneDPTruncatedAlgebra (hpos : 0 < p) (hp : (p : A) = 0) : Algebra T₀ DA :=
  (rankOneDPTruncatedMap hpos hp).toRingHom.toAlgebra

/-- 指定した切断多項式作用と元の係数環の作用は、実スカラー塔をなす。 -/
theorem rankOneDPTruncated_isScalarTower (hpos : 0 < p) (hp : (p : A) = 0) :
    letI : Algebra T₀ DA := rankOneDPTruncatedAlgebra hpos hp
    IsScalarTower A T₀ DA := by
  let : Algebra T₀ DA := rankOneDPTruncatedAlgebra hpos hp
  exact IsScalarTower.of_algebraMap_eq (fun a ↦ (rankOneDPTruncatedMap hpos hp).commutes a |>.symm)

/-- 非零係数環での、実切断多項式環のFin pで添字付けた標準冪基底。 -/
def rankOneDPTruncatedBasis (p : ℕ) (A : Type u) [CommRing A] [Nontrivial A] :
    Module.Basis (Fin p) A (AdjoinRoot ((Polynomial.X : Polynomial A) ^ p)) :=
  ((AdjoinRoot.powerBasis' (Polynomial.monic_X_pow p)).basis).reindex
    (finCongr (Polynomial.natDegree_X_pow (R := A) p))

/-- 標準冪基底の各元は、切断多項式環の実根のr乗。 -/
theorem rankOneDPTruncatedBasis_apply [Nontrivial A] (r : Fin p) :
    rankOneDPTruncatedBasis p A r =
      AdjoinRoot.root ((Polynomial.X : Polynomial A) ^ p) ^ (r : ℕ) := by
  rw [rankOneDPTruncatedBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
  rfl

/-- 標準冪基底の作用像は、一次分冪生成元の対応する冪。 -/
theorem rankOneDPTruncatedMap_basis [Nontrivial A] (hpos : 0 < p) (hp : (p : A) = 0)
    (r : Fin p) :
    rankOneDPTruncatedMap hpos hp (rankOneDPTruncatedBasis p A r) =
      DividedPowerAlgebra.dp A 1 (1 : A) ^ (r : ℕ) := by
  rw [rankOneDPTruncatedBasis_apply, map_pow, rankOneDPTruncatedMap_root]

end SerrePositivity.BhattScholze
