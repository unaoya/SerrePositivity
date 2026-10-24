module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassFixedZeroPaths
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightViaAImageMap
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellImageForwardZero

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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (lowerFunctor R n hn)) i m hi)
  (d : PostnikovCommonLayerInverse R hn f c) {j : ℕ} (hj : j ≤ i)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

lemma postnikovCommonClassFixedStandardMapped_original_hom :
    (postnikovCommonClassFixedStandardMappedRelative R hn f c d hj).hom =
    postnikovCommonRightImageToSecond R hn f c d ≫
      (postnikovCellImageRelative R (A.obj i).obj (A.obj j).obj
        (postnikovCommonClassBase R hn f c d) n hn
        (roofRefine R hn f c d.zero.source_le).roof.numerator
        (A.transition hj).hom).hom ≫ Path.map R
      (postnikovCommonClassTransitionToZero R hn f c d hj) ≫
        Path.map R (postnikovZeroClassMap R n 1 (f.app j).hom) := by
  simp only [postnikovCommonClassFixedStandardMappedRelative, SquareZero.RelativeWitness.mapOver,
    SquareZero.RelativeWitness.precomp, postnikovCommonClassStandardRelative,
    postnikovCommonClassStandardWitness, Path.Witness.precomp, Path.Witness.postcomp,
    Path.Witness.precompNonpositiveCell, postnikovCellImageRelative_hom,
    postnikovCommonClassFixedZeroMap, Path.map_comp, postnikovCommonRightImageToSecond_eq,
    postnikovCommonRightToClassifying, Category.assoc,
    reassoc_of% cellPathNonpositiveToCell_projection]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
