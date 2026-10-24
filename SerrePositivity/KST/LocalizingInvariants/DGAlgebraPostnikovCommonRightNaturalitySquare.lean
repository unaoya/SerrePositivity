module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellClassCompositionCongr
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassStandardSquare

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightNaturalitySquare
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：元の f の自然性正方形の二つの因子分解に、同じ直接 class 経路を与える。
方針：A の遷移と f、f と B の遷移の合成が一致する元の自然性を使う。
規約：同じ元の分子・共通底を保つ。使われ方：Γ の右側の二つの経路比較の基準。
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

lemma postnikovCommonRightNaturalitySquare_direct :
    (postnikovCellCompositionClassDirect R (A.obj i).obj (A.obj j).obj (B.obj j).obj
      (postnikovCommonClassBase R f c d) 1 (by omega)
      (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator
      (A.transition hj).hom (f.app j).hom).hom =
    (postnikovCellCompositionClassDirect R (A.obj i).obj (B.obj i).obj (B.obj j).obj
      (postnikovCommonClassBase R f c d) 1 (by omega)
      (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator
      (f.app i).hom (B.transition hj).hom).hom :=
  PostnikovCommonCore.postnikovCommonRightNaturalitySquare_direct
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
