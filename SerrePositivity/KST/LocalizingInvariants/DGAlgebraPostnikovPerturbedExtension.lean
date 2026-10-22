module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroConeDerivation
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerActions

/-!
概要：Postnikov の層包含を微分へ組み込んだ、実非可換 dg 代数を構成する。
方針：単一の負次数にある層の作用素について証明した derivation 則を適用する。
規約：底への準同型比較と class は後続。使われ方：非分裂 Postnikov 拡大の模型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n)

def postnikovPerturbedExtension : Mon (Complex R) := by
  have : (postnikovLayerBimodule R B n).X.IsStrictlyGE (-(n + 1)) :=
    postnikovLayer_lowerBound R B n
  have : (postnikovLayerBimodule R B n).X.IsStrictlyLE (-(n + 1)) :=
    postnikovLayer_upperBound R B n
  exact SquareZeroCone.algebra (postnikov R B (n + 1)) (postnikovLayerBimodule R B n)
    (postnikovLayerInclusionBimodule R B n) (-(n + 1)) (by omega)

lemma postnikovPerturbedExtension_d (p : ℤ) :
    (postnikovPerturbedExtension R B n hn).X.d p (p + 1) =
      (SquareZeroCone.splitAlgebra (postnikov R B (n + 1))
        (postnikovLayerBimodule R B n)).X.d p (p + 1) +
      (SquareZeroCone.operator (postnikov R B (n + 1)) (postnikovLayerBimodule R B n)
        (postnikovLayerInclusion R B n)).v p (p + 1) rfl := by
  exact perturbComplex_d _ _
    (SquareZeroCone.operator_closed (postnikov R B (n + 1)) (postnikovLayerBimodule R B n)
      (postnikovLayerInclusion R B n))
    (SquareZeroCone.operator_square_zero (postnikov R B (n + 1)) (postnikovLayerBimodule R B n)
      (postnikovLayerInclusion R B n)) p

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
