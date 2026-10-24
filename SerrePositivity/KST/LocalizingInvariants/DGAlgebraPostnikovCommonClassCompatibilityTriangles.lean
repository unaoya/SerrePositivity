module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassCompatibility

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassCompatibilityTriangles
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：標準 class に整合した新しい係数逆が、元の層の左右三角形を満たすことを示す。
方針：同じ実逆 d の三角形と A の遷移の自然性を、元の整数 shift で写す。
規約：class 経路で使った係数を取り替えない。使われ方：元の二切断射の実逆。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

lemma postnikovCommonClassCompatibilityCoefficient_hom :
    (postnikovCommonClassCompatibilityCoefficient R f c d (hj := hj)).hom =
      d.coefficient.hom⟦(1 : ℤ)⟧' ≫
        (postnikovLayerMap R (A.transition hj).hom 1)⟦(1 : ℤ)⟧' :=
  PostnikovCommonCore.postnikovCommonClassCompatibilityCoefficient_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonClassCompatibilityCoefficient_left :
    (postnikovLayerMap R (f.app d.zero.stage).hom 1)⟦(1 : ℤ)⟧' ≫
      (postnikovCommonClassCompatibilityCoefficient R f c d (hj := hj)).hom =
        (postnikovLayerMap R
          (A.transition (hj.trans (d.zero.inverse_le.trans d.zero.stage_le))).hom 1)⟦(1 : ℤ)⟧' :=
  PostnikovCommonCore.postnikovCommonClassCompatibilityCoefficient_left
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonClassCompatibilityCoefficient_right :
    (postnikovCommonClassCompatibilityCoefficient R f c d (hj := hj)).hom ≫
      (postnikovLayerMap R (f.app j).hom 1)⟦(1 : ℤ)⟧' =
        (postnikovLayerMap R
          (B.transition (hj.trans (d.zero.inverse_le.trans d.zero.stage_le))).hom 1)⟦(1 : ℤ)⟧' :=
  PostnikovCommonCore.postnikovCommonClassCompatibilityCoefficient_right
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
