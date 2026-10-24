module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassStandardZeroGlue
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessPrecomp

/-!
概要：遷移比較と標準 class 比較を、同じ共通底上で直接 affine 合成する。
方針：既存の二経路を相対証人へ束ね、その逆と合成を元の貼合せ源へ前合成する。
規約：旧 cellComp との一致は仮定しない。使われ方：元の class 経路の差の明示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Preadditive
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (lowerFunctor R n hn)) i m hi)
  (d : PostnikovCommonLayerInverse R hn f c) {j : ℕ} {hj : j ≤ i}
  (e : PostnikovZeroLayerInverse R n f j i hj)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

def postnikovCommonClassTransitionRelative : SquareZero.RelativeWitness
    (postnikovCommonRightZeroGlueProjection R hn f c d)
    (postnikovCommonClassTransitionLayer R hn f c d hj)
    (postnikovCommonClassTransitionTarget R hn f c d (hj := hj))
    (postnikovCommonClassTransitionSource R hn f c d (hj := hj)) where
  toWitness := postnikovCommonClassTransitionWitness R hn f c d e
  projection_eq := postnikovCommonClassTransitionWitness_projection R hn f c d e

def postnikovCommonClassStandardRelative : SquareZero.RelativeWitness
    (postnikovCommonRightZeroGlueProjection R hn f c d)
    (postnikovCommonClassTransitionLayer R hn f c d hj)
    (postnikovCommonClassTransitionTarget R hn f c d (hj := hj))
    (postnikovCommonClassStandardEndpoint R hn f c d hj) where
  toWitness := postnikovCommonClassStandardWitness R hn f c d hj
  projection_eq := postnikovCommonClassStandardWitness_projection R hn f c d hj

def postnikovCommonClassAffineRelative : SquareZero.RelativeWitness
    (postnikovCommonRightZeroGlueProjection R hn f c d)
    (postnikovCommonClassTransitionLayer R hn f c d hj)
    (postnikovCommonClassTransitionSource R hn f c d (hj := hj))
    (postnikovCommonClassStandardEndpoint R hn f c d hj) :=
  (postnikovCommonClassTransitionRelative R hn f c d e).reverse.comp
    (postnikovCommonClassStandardRelative R hn f c d (hj := hj))

def postnikovCommonClassAffineGlueRelative : SquareZero.RelativeWitness
    (postnikovCommonClassStandardGlueProjection R hn f c d)
    (postnikovCommonClassTransitionLayer R hn f c d hj)
    (postnikovCommonClassStandardGlueLeft R hn f c d (hj := hj))
    (postnikovCommonClassStandardGlueRight R hn f c d (hj := hj)) :=
  (postnikovCommonClassAffineRelative R hn f c d e).precomp
    (cellPathNonpositiveProjection R (postnikovCommonRightZeroGlueSource R hn f c d))

lemma postnikovCommonClassAffineRelative_hom_linear :
    (postnikovCommonClassAffineRelative R hn f c d e).hom.hom =
      (postnikovCommonClassTransitionSource R hn f c d (hj := hj) ≫ Path.diagonal R _).hom -
        (postnikovCommonClassTransitionWitness R hn f c d e).hom.hom +
        (postnikovCommonClassStandardWitness R hn f c d hj).hom.hom := by
  change (((postnikovCommonClassTransitionRelative R hn f c d e).reverse).comp _).hom.hom = _
  rw [SquareZero.RelativeWitness.comp_hom_linear, SquareZero.RelativeWitness.reverse_hom_linear]
  change (postnikovCommonClassTransitionTarget R hn f c d (hj := hj) ≫ Path.diagonal R _).hom -
      (postnikovCommonClassTransitionWitness R hn f c d e).hom.hom +
      (postnikovCommonClassTransitionSource R hn f c d (hj := hj) ≫ Path.diagonal R _).hom -
      (postnikovCommonClassTransitionTarget R hn f c d (hj := hj) ≫ Path.diagonal R _).hom +
      (postnikovCommonClassStandardWitness R hn f c d hj).hom.hom = _
  abel

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
