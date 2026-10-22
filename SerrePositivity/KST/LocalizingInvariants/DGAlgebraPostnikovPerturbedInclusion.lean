module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovPerturbedClassComparison
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroConeInclusion

/-!
概要：元の隣接 Postnikov 上段を摂動代数へ包含し、元の射影と零切断への class を保つ。
方針：実零切断の微分変更に沿う移送を、元の層包含へ適用する。
規約：実代数射の等式を保持。使われ方：元の上段を頂点とする実代数 pullback。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex CochainComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n)

local instance inclusionLayerLower :
    (postnikovLayerBimodule R B n).X.IsStrictlyGE (-(n + 1)) := postnikovLayer_lowerBound R B n
local instance inclusionLayerUpper :
    (postnikovLayerBimodule R B n).X.IsStrictlyLE (-(n + 1)) := postnikovLayer_upperBound R B n

def postnikovPerturbedInclusion : postnikov R B (n + 1) ⟶ postnikovPerturbedExtension R B n hn :=
  SquareZeroCone.inclusion (postnikov R B (n + 1)) (postnikovLayerBimodule R B n)
    (postnikovLayerInclusionBimodule R B n) (-(n + 1)) (by omega)

lemma postnikovPerturbedInclusion_mono : Mono (postnikovPerturbedInclusion R B n hn).hom :=
  SquareZeroCone.inclusion_mono _ _ _ _ _

lemma postnikovPerturbedInclusion_toCone : (postnikovPerturbedInclusion R B n hn).hom ≫
    (postnikovPerturbedExtensionComplexIso R B n hn).hom =
      mappingCone.inr (postnikovLayerInclusion R B n) := SquareZeroCone.inclusion_toCone _ _ _ _ _

lemma postnikovPerturbedInclusion_projection : postnikovPerturbedInclusion R B n hn ≫
    postnikovPerturbedProjection R B n hn = postnikovTransition R B (n + 1) n (by omega) :=
  SquareZeroCone.inclusion_quotient _ _ _ _ _ _ _

lemma postnikovPerturbedInclusion_class : postnikovPerturbedInclusion R B n hn ≫
    postnikovPerturbedClass R B n hn = postnikovTransition R B (n + 1) n (by omega) ≫
      SquareZero.zeroSection (postnikov R B n) (postnikovShiftedLayerBimodule R B n hn 1) :=
  SquareZeroCone.inclusion_class _ _ _ _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
