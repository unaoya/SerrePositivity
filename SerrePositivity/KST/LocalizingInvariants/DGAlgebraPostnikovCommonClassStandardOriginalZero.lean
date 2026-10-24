module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassFixedZeroPaths
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightViaAImageMap
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellImageForwardZero

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassStandardOriginalZero
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：fixed Γ の標準経路の右像を、元の A 遷移の ImageWitness の零底像へ同定する。
方針：元の標準証人の前合成射を、同じ Γ の二重 cell 射へ厳密に揃える。
規約：元の標準経路と全射を保持。使われ方：分子 ViaA の第一自然性との比較。
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

lemma postnikovCommonClassFixedStandardMapped_original_hom :
    (postnikovCommonClassFixedStandardMappedRelative R f c d hj).hom =
    postnikovCommonRightImageToSecond R f c d ≫
      (postnikovCellImageRelative R (A.obj i).obj (A.obj j).obj
        (postnikovCommonClassBase R f c d) 1 (by omega)
        (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator
        (A.transition hj).hom).hom ≫ Path.map R
      (postnikovCommonClassTransitionToZero R f c d hj) ≫
        Path.map R (postnikovZeroClassMap R 1 1 (f.app j).hom) :=
  PostnikovCommonCore.postnikovCommonClassFixedStandardMapped_original_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
