module
public import SerrePositivity.KST.SConstruction.CubeLeftKeep

/-! # 元の有限鎖立方体の連結 tensor 比較
概要：n+m 次元の元の鎖立方体と、n 次元・m 次元の tensor の因子順を保つ結合比較を作る。
方針：右側の次元で帰納し、元の右単位と結合同型だけを合成する。
規約：交差や座標反転は使わない。使われ方：立方体圏の連結積を鎖複体へ移す比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の鎖立方体の因子順を保つ、連結と tensor の余モノイド同型。 -/
def serreCubeTensorIso (n : ℕ) : (m : ℕ) →
    serreCubeComonoid A (n + m) ≅ serreCubeComonoid A n ⊗ serreCubeComonoid A m
  | 0 => (ρ_ (serreCubeComonoid A n)).symm
  | m + 1 => (serreCubeTensorIso n m ⊗ᵢ Iso.refl (serreIntervalComonoid A)) ≪≫
      α_ (serreCubeComonoid A n) (serreCubeComonoid A m) (serreIntervalComonoid A)

/-- 零個の右因子では、元の右単位比較を回収する。 -/
lemma serreCubeTensorIso_zero (n : ℕ) :
    serreCubeTensorIso A n 0 = (ρ_ (serreCubeComonoid A n)).symm := rfl

/-- 右因子を一つ増やした比較は、元の tensor と結合替えの合成。 -/
lemma serreCubeTensorIso_succ (n m : ℕ) :
    serreCubeTensorIso A n (m + 1) =
      (serreCubeTensorIso A n m ⊗ᵢ Iso.refl (serreIntervalComonoid A)) ≪≫
        α_ (serreCubeComonoid A n) (serreCubeComonoid A m) (serreIntervalComonoid A) := rfl

end SerrePositivity.KST.SConstruction
