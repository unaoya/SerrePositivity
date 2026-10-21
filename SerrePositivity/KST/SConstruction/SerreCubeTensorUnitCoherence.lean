module
public import SerrePositivity.KST.SConstruction.SerreCubeDimensionTransport
public import SerrePositivity.KST.SConstruction.SerreCubeTensorHomValues
public import SerrePositivity.KST.SConstruction.MonoidalPowerCoherenceStep

/-! # 元の連結鎖比較と左右単位の整合性
概要：元の零次元立方体の単位と、同じ連結比較の左右単位との可換性を証明する。
方針：右単位は零段の定義から、左単位は元の次元移送を保つ右端保持の帰納から得る。
規約：元の Serre 比較を保つ。使われ方：具体的立方体関手の強モノイダル構造。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の連結比較は、元の左単位の次元移送と可換。 -/
lemma serreCubeTensor_leftUnit (m : ℕ) :
    serreCubeDimensionMap A (Nat.zero_add m) =
      (serreCubeTensorIso A 0 m).hom ≫ (λ_ (serreCubeComonoid A m)).hom := by
  induction m with
  | zero =>
    exact monoidalPowerCoherence_leftUnit_zero (C := Comon (Complex A))
  | succ m ih =>
    have ht := monoidalPowerCoherence_leftUnit_step (R := serreCubeComonoid A (0 + m))
      (Y := serreCubeComonoid A m) (I := serreIntervalComonoid A)
      (serreCubeTensorIso A 0 m).hom
    erw [serreCubeDimensionMap_zero_add_succ A m, ih, serreCubeTensorIso_succ_hom A 0 m]
    dsimp only [serreCubeRightTensorMap]
    apply Comon.ext
    exact congrArg (fun f => f.hom) ht.symm

/-- 元の連結比較は、元の右単位の次元移送と可換。 -/
lemma serreCubeTensor_rightUnit (n : ℕ) :
    serreCubeDimensionMap A (rfl : n + 0 = n) =
      (serreCubeTensorIso A n 0).hom ≫ (ρ_ (serreCubeComonoid A n)).hom := by
  change 𝟙 (serreCubeComonoid A n) =
    (ρ_ (serreCubeComonoid A n)).inv ≫ (ρ_ (serreCubeComonoid A n)).hom
  exact (ρ_ (serreCubeComonoid A n)).inv_hom_id.symm

end SerrePositivity.KST.SConstruction
