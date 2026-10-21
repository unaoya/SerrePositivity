module
public import SerrePositivity.KST.SConstruction.SerreCubeOrientationSigns
public import SerrePositivity.DifferentialGraded.Category.Components

/-! # 元の向き補正と dg の通常順合成
概要：二区間の向き補正と豊穣順の合成を、native dg nerve の通常順合成で回収する。
方針：元の斉次合成の双線形性と、元の二次数の Koszul 符号を使う。
規約：同じ元の dg 圏の合成を保持。使われ方：HA 方程式の分割合成項。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の豊穣順合成は、元の整数単位による二つの符号の積を保つ。 -/
lemma serreCubeForward_units_smul {x y z : D} {p q k : ℤ}
    (f : GradedHom A x y p) (g : GradedHom A y z q) (hk : p + q = k) (s t : ℤˣ) :
    forward A (s • f) (t • g) hk = (s * t) • forward A f g hk := by
  unfold forward
  simp only [Units.smul_def, TensorProduct.smul_tmul, TensorProduct.tmul_smul,
    map_zsmul, smul_smul, Units.val_mul, mul_comm]

/-- 元の二つの向き補正した成分の通常順合成は、連結次元の向き補正した豊穣合成。 -/
lemma serreCubeOriented_compose {x y z : D} (p q : ℕ) (k : ℤ)
    (hk : -(p : ℤ) + -(q : ℤ) = k)
    (f : GradedHom A x y (-(p : ℤ))) (g : GradedHom A y z (-(q : ℤ))) :
    compose A (serreCubeOrientationSign q • g) (serreCubeOrientationSign p • f) hk =
      serreCubeOrientationSign (p + q) • forward A f g hk := by
  change ((-(p : ℤ)) * (-(q : ℤ))).negOnePow •
    forward A (serreCubeOrientationSign p • f) (serreCubeOrientationSign q • g) hk = _
  rw [serreCubeForward_units_smul, smul_smul]
  apply congrArg (fun s => s • forward A f g hk)
  rw [neg_mul_neg, mul_comm]
  exact (serreCubeOrientationSign_add p q).symm

end SerrePositivity.KST.SConstruction
