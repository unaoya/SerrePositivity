module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassStandardZeroGlue
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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} {hj : j ≤ i}
  (e : PostnikovZeroLayerInverse R 1 f j i hj)

def postnikovCommonClassTransitionRelative : SquareZero.RelativeWitness
    (postnikovCommonRightZeroGlueProjection R f c d)
    (postnikovCommonClassTransitionLayer R f c d hj)
    (postnikovCommonClassTransitionTarget R f c d (hj := hj))
    (postnikovCommonClassTransitionSource R f c d (hj := hj)) where
  toWitness := postnikovCommonClassTransitionWitness R f c d e
  projection_eq := postnikovCommonClassTransitionWitness_projection R f c d e

def postnikovCommonClassStandardRelative : SquareZero.RelativeWitness
    (postnikovCommonRightZeroGlueProjection R f c d)
    (postnikovCommonClassTransitionLayer R f c d hj)
    (postnikovCommonClassTransitionTarget R f c d (hj := hj))
    (postnikovCommonClassStandardEndpoint R f c d hj) where
  toWitness := postnikovCommonClassStandardWitness R f c d hj
  projection_eq := postnikovCommonClassStandardWitness_projection R f c d hj

def postnikovCommonClassAffineRelative : SquareZero.RelativeWitness
    (postnikovCommonRightZeroGlueProjection R f c d)
    (postnikovCommonClassTransitionLayer R f c d hj)
    (postnikovCommonClassTransitionSource R f c d (hj := hj))
    (postnikovCommonClassStandardEndpoint R f c d hj) :=
  (postnikovCommonClassTransitionRelative R f c d e).reverse.comp
    (postnikovCommonClassStandardRelative R f c d (hj := hj))

def postnikovCommonClassAffineGlueRelative : SquareZero.RelativeWitness
    (postnikovCommonClassStandardGlueProjection R f c d)
    (postnikovCommonClassTransitionLayer R f c d hj)
    (postnikovCommonClassStandardGlueLeft R f c d (hj := hj))
    (postnikovCommonClassStandardGlueRight R f c d (hj := hj)) :=
  (postnikovCommonClassAffineRelative R f c d e).precomp
    (cellPathNonpositiveProjection R (postnikovCommonRightZeroGlueSource R f c d))

lemma postnikovCommonClassAffineRelative_hom_linear :
    (postnikovCommonClassAffineRelative R f c d e).hom.hom =
      (postnikovCommonClassTransitionSource R f c d (hj := hj) ≫ Path.diagonal R _).hom -
        (postnikovCommonClassTransitionWitness R f c d e).hom.hom +
        (postnikovCommonClassStandardWitness R f c d hj).hom.hom := by
  change (((postnikovCommonClassTransitionRelative R f c d e).reverse).comp _).hom.hom = _
  rw [SquareZero.RelativeWitness.comp_hom_linear, SquareZero.RelativeWitness.reverse_hom_linear]
  change (postnikovCommonClassTransitionTarget R f c d (hj := hj) ≫ Path.diagonal R _).hom -
      (postnikovCommonClassTransitionWitness R f c d e).hom.hom +
      (postnikovCommonClassTransitionSource R f c d (hj := hj) ≫ Path.diagonal R _).hom -
      (postnikovCommonClassTransitionTarget R f c d (hj := hj) ≫ Path.diagonal R _).hom +
      (postnikovCommonClassStandardWitness R f c d hj).hom.hom = _
  abel

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
