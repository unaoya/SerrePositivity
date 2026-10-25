module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConvolutionLimits
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovAlgebraPullback

/-!
概要：元の Postnikov 錐を実乗法的写像の単体集合に送った厳密極限を示す。
方針：元の代数 pullback 錐と畳み込み・表現可能関手の極限保存を用いる。
規約：厳密極限を導来写像空間の homotopy pullback と同一視しない。
使われ方：同じ頂点・二脚を保つ導来比較の前段。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n)

def postnikovMultiplicativeMappingCone : Cone
    (cospan (postnikovPerturbedClass R B n hn)
      (SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn 1)) ⋙
        multiplicativeMappingFunctor R A) :=
  (multiplicativeMappingFunctor R A).mapCone (postnikovAlgebraPullbackCone R B n hn)

def postnikovMultiplicativeMappingCone_isLimit :
    IsLimit (postnikovMultiplicativeMappingCone R A B n hn) :=
  isLimitOfPreserves (multiplicativeMappingFunctor R A)
    (postnikovAlgebraPullback_isLimit R B n hn)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
