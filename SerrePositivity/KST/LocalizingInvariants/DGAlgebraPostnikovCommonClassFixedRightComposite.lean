module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassFixedRightNaturality

/-!
概要：元の fixed class 互換性と fⱼ の自然性の合成を、G⁻¹⋅標準自然性へ全射で同定する。
方針：元の互換性の反転合成式と、移送後の affine 結合則を使う。
規約：元の native 互換性・自然性の全射を保持。使われ方：元の W を接ぐ右三角形。
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

def postnikovCommonClassGlueStandardPath :=
  (postnikovCommonRightGlueZeroRelative R f c d hj).reverse.comp
    (postnikovCommonClassStandardContourPath R f c d hj)

variable (e : PostnikovZeroLayerInverse R 1 f j i hj)

lemma postnikovCommonClassFixedCompatibilityNaturality_hom :
    (postnikovCommonClassFixedCompatibilityNaturality R f c d hj e).hom =
      (postnikovCommonClassGlueStandardPath R f c d hj).hom := by
  let v := postnikovCommonClassFixedTransitionMappedRelative R f c d hj e
  let s := postnikovCommonClassFixedStandardMappedRelative R f c d hj
  let n := postnikovCommonClassFixedRightNaturality R f c d hj
  have hc := SquareZero.RelativeWitness.comp_congr_hom_of_paths
    (v := postnikovCommonClassFixedCompatibilityMappedRelative R f c d hj e)
    (w := n) (v' := v.reverse.comp s) (w' := n)
    (postnikovCommonClassFixedCompatibilityMapped_hom R f c d hj e) rfl
  have ha := SquareZero.RelativeWitness.comp_assoc_hom v.reverse s n
  have hh := SquareZero.RelativeWitness.comp_congr_hom_of_paths
    (v := v.reverse) (w := s.comp n)
    (v' := (postnikovCommonRightGlueZeroRelative R f c d hj).reverse)
    (w' := postnikovCommonClassStandardContourPath R f c d hj)
    (postnikovCommonClassFixedTransitionMapped_reverse_glue R f c d hj e)
    (postnikovCommonClassFixedStandardNaturality_hom R f c d hj)
  exact hc.trans (ha.trans hh)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
