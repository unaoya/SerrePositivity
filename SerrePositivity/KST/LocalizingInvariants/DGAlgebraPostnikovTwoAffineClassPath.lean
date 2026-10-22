module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassAffine
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRelativeClassMap

/-!
概要：元の二切断 class データに、同じ源・端点・底を持つ直接 affine 貼合せを供給する。
方針：既存の遷移比較・標準比較を同じ共通源へ移し、元の Γ の class 像へ同定する。
規約：元の classWitness の射との一致は主張しない。使われ方：経路の差の実補正。
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

def classAffineRelativeWitness : SquareZero.RelativeWitness
    (d.classProjection R) (d.numeratorLayer R)
    (d.imageClass R) (d.targetClass R) where
  hom := (postnikovCommonClassAffineGlueRelative R f d.baseInverse d.layerInverse
      d.inverse).hom
  source_eq :=
    (postnikovCommonClassAffineGlueRelative R f d.baseInverse d.layerInverse
      d.inverse).source_eq.trans
      (d.sourceClass_coefficient R).symm
  target_eq :=
    (postnikovCommonClassAffineGlueRelative R f d.baseInverse d.layerInverse
      d.inverse).target_eq
  projection_eq :=
    (postnikovCommonClassAffineGlueRelative R f d.baseInverse d.layerInverse
      d.inverse).projection_eq

/-- 元の経路と直接貼合せの差を、標準 class 上の元の相対ループとして保持する。 -/
def classAffineDefect : SquareZero.RelativeWitness (d.classProjection R) (d.numeratorLayer R)
    (d.targetClass R) (d.targetClass R) :=
  (d.classRelativeWitness R).reverse.comp (d.classAffineRelativeWitness R)

lemma classAffineDefect_correction :
    ((d.classRelativeWitness R).comp (d.classAffineDefect R)).hom =
      (d.classAffineRelativeWitness R).hom := by
  apply Mon.Hom.ext
  change ((d.classRelativeWitness R).comp
    ((d.classRelativeWitness R).reverse.comp (d.classAffineRelativeWitness R))).hom.hom = _
  rw [SquareZero.RelativeWitness.comp_hom_linear, SquareZero.RelativeWitness.comp_hom_linear,
    SquareZero.RelativeWitness.reverse_hom_linear]
  abel

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
