module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassFixedTransition
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoAffineClassCorrection

/-!
概要：指定右経路を使う class 互換性から、元の Γ の実相対模型射を組み直す。
方針：同じ係数と両 class に新経路を渡し、旧模型射との差を実補正同型で保持する。
規約：補正の場所は targetRelativeModel。使われ方：整合する二切断の逆候補。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Preadditive
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

def classFixedRelativeWitness : SquareZero.RelativeWitness
    (d.classProjection R) (d.numeratorLayer R) (d.imageClass R) (d.targetClass R) where
  hom := (postnikovCommonClassFixedGlueCompatibility R f d.baseInverse d.layerInverse d.inverse).hom
  source_eq :=
    (postnikovCommonClassFixedGlueCompatibility R f d.baseInverse d.layerInverse
      d.inverse).source_eq.trans (d.sourceClass_coefficient R).symm
  target_eq :=
    (postnikovCommonClassFixedGlueCompatibility R f d.baseInverse d.layerInverse
      d.inverse).target_eq
  projection_eq :=
    (postnikovCommonClassFixedGlueCompatibility R f d.baseInverse d.layerInverse
      d.inverse).projection_eq

def classFixedDefect : SquareZero.RelativeWitness (d.classProjection R) (d.numeratorLayer R)
    (d.targetClass R) (d.targetClass R) :=
  (d.classRelativeWitness R).reverse.comp (d.classFixedRelativeWitness R)

lemma classFixedDefect_correction :
    ((d.classRelativeWitness R).comp (d.classFixedDefect R)).hom =
      (d.classFixedRelativeWitness R).hom := by
  apply Mon.Hom.ext
  change ((d.classRelativeWitness R).comp
    ((d.classRelativeWitness R).reverse.comp (d.classFixedRelativeWitness R))).hom.hom = _
  rw [SquareZero.RelativeWitness.comp_hom_linear, SquareZero.RelativeWitness.comp_hom_linear,
    SquareZero.RelativeWitness.reverse_hom_linear]
  abel

def classFixedTargetCorrection : d.targetRelativeModel R ≅ d.targetRelativeModel R :=
  SquareZeroExtension.transportIso (d.numeratorLayer R) (d.classFixedDefect R)

def sourceToTargetFixedRelative : d.sourceRelativeModel R ⟶ d.targetRelativeModel R :=
  SquareZeroExtension.classModelMap (d.classCoefficient R) (d.sourceClass R) (d.targetClass R)
    (d.classFixedRelativeWitness R)

lemma sourceToTargetFixedRelative_correction : d.sourceToTargetRelative R ≫
    (d.classFixedTargetCorrection R).hom = d.sourceToTargetFixedRelative R := by
  change SquareZeroExtension.classModelMap (d.classCoefficient R) (d.sourceClass R)
      (d.targetClass R) (d.classRelativeWitness R) ≫
      SquareZeroExtension.transport (d.numeratorLayer R) (d.classFixedDefect R) = _
  rw [SquareZeroExtension.classModelMap_postTransport]
  exact SquareZeroExtension.classModelMap_congr _ _ _ _ (d.classFixedDefect_correction R)

lemma sourceToTargetFixedRelative_left : d.sourceToTargetFixedRelative R ≫
    SquareZeroExtension.relativeLeft (d.numeratorLayer R) (d.targetClass R) =
      SquareZeroExtension.relativeLeft (d.denominatorLayer R) (d.sourceClass R) :=
  SquareZeroExtension.classModelMap_left _ _ _ _

lemma sourceToTargetFixedRelative_right : d.sourceToTargetFixedRelative R ≫
    SquareZeroExtension.relativeRight (d.numeratorLayer R) (d.targetClass R) =
      SquareZeroExtension.relativeRight (d.denominatorLayer R) (d.sourceClass R) :=
  SquareZeroExtension.classModelMap_right _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
