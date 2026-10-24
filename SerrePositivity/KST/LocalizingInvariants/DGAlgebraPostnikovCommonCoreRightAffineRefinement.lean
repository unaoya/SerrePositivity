module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightAffineCompositeSquare
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightComparisonRefinement
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquarePrecomp

/-!
概要：A 遷移と f の二因子分解の affine 比較を、元の Γ の源へ移す。
方針：指定した細分射を前合成し、元の Γ 射影へ等式で移す。
規約：係数は合成射による制限のまま。使われ方：零底の貼合せ比較への次の係数移送。
-/

@[expose] public section
noncomputable section
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

def postnikovCommonRightAffineRefinedSource :=
  postnikovCommonRightToFactorization R hn f c d ≫
    postnikovCommonRightNaturalityCompositeSource R hn f c d hj

def postnikovCommonRightAffineRefinedTarget :=
  postnikovCommonRightToFactorization R hn f c d ≫
    postnikovCommonRightNaturalityCompositeTarget R hn f c d hj

def postnikovCommonRightAffineRefinedViaA : SquareZero.RelativeWitness
    (postnikovCommonClassStandardGlueProjection R hn f c d)
    (postnikovCommonRightNaturalityCompositeLayer R hn f c d hj)
    (postnikovCommonRightAffineRefinedSource R hn f c d hj)
    (postnikovCommonRightAffineRefinedTarget R hn f c d hj) :=
  ((postnikovCommonRightAffineNaturalityViaA R hn f c d hj).precomp
    (postnikovCommonRightToFactorization R hn f c d)).rebase
    (postnikovCommonRightToFactorization_projection R hn f c d)

def postnikovCommonRightAffineRefinedViaB : SquareZero.RelativeWitness
    (postnikovCommonClassStandardGlueProjection R hn f c d)
    (postnikovCommonRightNaturalityCompositeLayer R hn f c d hj)
    (postnikovCommonRightAffineRefinedSource R hn f c d hj)
    (postnikovCommonRightAffineRefinedTarget R hn f c d hj) :=
  ((postnikovCommonRightAffineNaturalityViaB R hn f c d hj).precomp
    (postnikovCommonRightToFactorization R hn f c d)).rebase
    (postnikovCommonRightToFactorization_projection R hn f c d)

/-- 元の Γ 源と射影の上で、二つの affine 合成経路を結ぶ実二重経路。 -/
def postnikovCommonRightAffineRefinedSquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonRightAffineRefinedViaA R hn f c d hj)
    (postnikovCommonRightAffineRefinedViaB R hn f c d hj) :=
  ((postnikovCommonRightAffineCompositeSquare R hn f c d hj).precomp
    (postnikovCommonRightToFactorization R hn f c d)).rebase
    (postnikovCommonRightToFactorization_projection R hn f c d)

def postnikovCommonRightAffineRefinedTransportHomotopy : Path.Witness R
    (SquareZeroExtension.transport (postnikovCommonRightNaturalityCompositeLayer R hn f c d hj)
      (postnikovCommonRightAffineRefinedViaA R hn f c d hj))
    (SquareZeroExtension.transport (postnikovCommonRightNaturalityCompositeLayer R hn f c d hj)
      (postnikovCommonRightAffineRefinedViaB R hn f c d hj)) :=
  SquareZeroExtension.transportHomotopy _ (postnikovCommonRightAffineRefinedSquare R hn f c d hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
