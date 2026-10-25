module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeMappingVertices
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConvolutionLimits
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovAlgebraPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
概要：元の Postnikov 上段の固定底写像と、元の class の指定零切断上の写像を同定する。
方針：元の実写像正方形の pullback と指定底の pullback を横に貼り合わせる。
規約：全単体の実同型であり、元の包含辺と指定底射影を保持する。
使われ方：Postnikov 拡大の導来比較で、指定底の相対性を元の模型へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n)

set_option maxHeartbeats 800000 in -- 元の Postnikov 代数錐と全 AW 写像関手の像を同定する。
lemma postnikovMultiplicativeMapping_isPullback :
    IsPullback (multiplicativeMappingPostcompose R A (postnikovPerturbedInclusion R B n hn))
      (multiplicativeMappingPostcompose R A (postnikovTransition R B (n + 1) n (by omega)))
      (multiplicativeMappingPostcompose R A (postnikovPerturbedClass R B n hn))
      (multiplicativeMappingPostcompose R A
        (SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn 1))) :=
  (IsPullback.of_isLimit (postnikovAlgebraPullback_isLimit R B n hn)).map
    (multiplicativeMappingFunctor R A)

variable (b : A ⟶ postnikov R B n)

lemma postnikovRelativeMultiplicativeMapping_isPullback :
    IsPullback
      (relativeMultiplicativeMappingProjection R
          (postnikovTransition R B (n + 1) n (by omega)) b ≫
        multiplicativeMappingPostcompose R A (postnikovPerturbedInclusion R B n hn))
      (relativeMultiplicativeMappingBaseProjection R
        (postnikovTransition R B (n + 1) n (by omega)) b)
      (multiplicativeMappingPostcompose R A (postnikovPerturbedClass R B n hn))
      (multiplicativeMappingBase R (b ≫
        SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn 1))) := by
  have h := (IsPullback.of_hasPullback
    (multiplicativeMappingPostcompose R A (postnikovTransition R B (n + 1) n (by omega)))
    (multiplicativeMappingBase R b)).paste_horiz
      (postnikovMultiplicativeMapping_isPullback R A B n hn)
  rw [multiplicativeMappingBase_postcompose] at h
  exact h

def postnikovRelativeMultiplicativeMappingIso :
    relativeMultiplicativeMappingSimplices R
      (postnikovTransition R B (n + 1) n (by omega)) b ≅
    relativeMultiplicativeMappingSimplices R (postnikovPerturbedClass R B n hn)
      (b ≫ SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn 1)) :=
  (postnikovRelativeMultiplicativeMapping_isPullback R A B n hn b).isoIsPullback _ _
    (IsPullback.of_hasPullback _ _)

@[reassoc]
lemma postnikovRelativeMultiplicativeMappingIso_projection :
    (postnikovRelativeMultiplicativeMappingIso R A B n hn b).hom ≫
      relativeMultiplicativeMappingProjection R (postnikovPerturbedClass R B n hn)
        (b ≫ SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn 1)) =
    relativeMultiplicativeMappingProjection R
        (postnikovTransition R B (n + 1) n (by omega)) b ≫
      multiplicativeMappingPostcompose R A (postnikovPerturbedInclusion R B n hn) :=
  (postnikovRelativeMultiplicativeMapping_isPullback R A B n hn b).isoIsPullback_hom_fst _ _ _

@[reassoc]
lemma postnikovRelativeMultiplicativeMappingIso_base :
    (postnikovRelativeMultiplicativeMappingIso R A B n hn b).hom ≫
      relativeMultiplicativeMappingBaseProjection R (postnikovPerturbedClass R B n hn)
        (b ≫ SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn 1)) =
    relativeMultiplicativeMappingBaseProjection R
      (postnikovTransition R B (n + 1) n (by omega)) b :=
  (postnikovRelativeMultiplicativeMapping_isPullback R A B n hn b).isoIsPullback_hom_snd _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
