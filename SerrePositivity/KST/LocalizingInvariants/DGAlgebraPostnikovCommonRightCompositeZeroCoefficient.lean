module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightAffineCompositeSquare
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightClassifyingBaseChange
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassBaseZeroIso
public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestrictionEqualityIso

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightCompositeZeroCoefficient
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：二因子分解の合成射の係数を、classifying 比較の元の零底係数へ同定する。
方針：f の自然性で底射を同定し、零切断への既存係数同型と恒等底射移送を合成する。
規約：元の P と underlying 係数恒等射を保持。使われ方：Γ 源上の比較の零底への移送。
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

abbrev postnikovCommonRightClassifyingLayer :=
  PostnikovCommonCore.postnikovCommonRightClassifyingLayer
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightComposite_zero_base :
    ((postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator ≫
      postnikovMap R (postnikovCommonRightNaturalityComposite R f hj) 1) ≫
        postnikovTransition R (B.obj j).obj 1 0 (by omega) =
      postnikovCommonRightClassifyingBase R f c d hj :=
  PostnikovCommonCore.postnikovCommonRightComposite_zero_base
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightCompositeZeroCoefficientIso :
    postnikovCommonRightNaturalityCompositeLayer R f c d hj ≅
      postnikovCommonRightClassifyingLayer R f c d hj :=
  PostnikovCommonCore.postnikovCommonRightCompositeZeroCoefficientIso
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightCompositeZeroCoefficientIso_hom :
    (postnikovCommonRightCompositeZeroCoefficientIso R f c d hj).hom.hom =
      𝟙 ((postnikovLayer R (B.obj j).obj 1)⟦(1 : ℤ)⟧) :=
  PostnikovCommonCore.postnikovCommonRightCompositeZeroCoefficientIso_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
