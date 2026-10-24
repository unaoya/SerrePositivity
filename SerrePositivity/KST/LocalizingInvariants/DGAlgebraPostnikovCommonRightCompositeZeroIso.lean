module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightCompositeZeroCoefficient
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroUnderlyingMaps

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightCompositeZeroIso
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：合成自然性の実平方零標的を、classifying 側の同じ零底標的へ写す同型。
方針：underlying 恒等の係数同型を平方零関手で写し、元の二つの射影を比較する。
規約：全 class 標的への射も保持。使われ方：全経路の零底への移送と照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

def postnikovCommonRightCompositeZeroIso :
    SquareZero.algebra (postnikovCommonClassBase R f c d)
      (postnikovCommonRightNaturalityCompositeLayer R f c d hj) ≅
    SquareZero.algebra (postnikovCommonClassBase R f c d)
      (postnikovCommonRightClassifyingLayer R f c d hj) :=
  PostnikovCommonCore.postnikovCommonRightCompositeZeroIso
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightCompositeZeroIso_projection :
    (postnikovCommonRightCompositeZeroIso R f c d hj).hom ≫ SquareZero.projection _ _ =
      SquareZero.projection _ _ :=
  PostnikovCommonCore.postnikovCommonRightCompositeZeroIso_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightCompositeZeroIso_inv_projection :
    (postnikovCommonRightCompositeZeroIso R f c d hj).inv ≫ SquareZero.projection _ _ =
      SquareZero.projection _ _ :=
  PostnikovCommonCore.postnikovCommonRightCompositeZeroIso_inv_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightCompositeZeroIso_hom :
    (postnikovCommonRightCompositeZeroIso R f c d hj).hom.hom =
      biprod.map (𝟙 (postnikovCommonClassBase R f c d).X)
        (𝟙 ((postnikovLayer R (B.obj j).obj 1)⟦(1 : ℤ)⟧)) :=
  PostnikovCommonCore.postnikovCommonRightCompositeZeroIso_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

/-- 底変更した class 標的への全射も元の零切断射と厳密に一致する。 -/
lemma postnikovCommonRightCompositeZeroIso_map :
    (postnikovCommonRightCompositeZeroIso R f c d hj).hom ≫
      SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1) =
    SquareZero.baseChangeMap
      ((postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator ≫
        postnikovMap R (postnikovCommonRightNaturalityComposite R f hj) 1)
      (postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1) ≫
        postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1 :=
  PostnikovCommonCore.postnikovCommonRightCompositeZeroIso_map
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
