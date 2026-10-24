module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorAffineClassPath
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeClassPostTransport

/-!
概要：元の Γ の模型射と直接 affine 貼合せの模型射との差を、実補正自同型で表す。
方針：実相対ループの輸送同型と class 模型射の後合成則を使う。
規約：補正は共通源の targetRelativeModel 上。τₙ₊₁Aⱼ 上の自同型とは主張しない。
使われ方：class 係数の修正と元の経路の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} {hn : 0 ≤ n} {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovSuccessorClassInverseData R hn f j)

def classAffineTargetCorrection : d.targetRelativeModel R ≅ d.targetRelativeModel R :=
  SquareZeroExtension.transportIso (d.numeratorLayer R) (d.classAffineDefect R)

def sourceToTargetAffineRelative : d.sourceRelativeModel R ⟶ d.targetRelativeModel R :=
  SquareZeroExtension.classModelMap (d.classCoefficient R) (d.sourceClass R) (d.targetClass R)
    (d.classAffineRelativeWitness R)

lemma sourceToTargetAffineRelative_correction : d.sourceToTargetRelative R ≫
    (d.classAffineTargetCorrection R).hom = d.sourceToTargetAffineRelative R := by
  change SquareZeroExtension.classModelMap (d.classCoefficient R) (d.sourceClass R)
      (d.targetClass R) (d.classRelativeWitness R) ≫
      SquareZeroExtension.transport (d.numeratorLayer R) (d.classAffineDefect R) = _
  rw [SquareZeroExtension.classModelMap_postTransport]
  exact SquareZeroExtension.classModelMap_congr _ _ _ _ (d.classAffineDefect_correction R)

lemma sourceToTargetAffineRelative_left : d.sourceToTargetAffineRelative R ≫
    SquareZeroExtension.relativeLeft (d.numeratorLayer R) (d.targetClass R) =
      SquareZeroExtension.relativeLeft (d.denominatorLayer R) (d.sourceClass R) :=
  SquareZeroExtension.classModelMap_left _ _ _ _

lemma sourceToTargetAffineRelative_right : d.sourceToTargetAffineRelative R ≫
    SquareZeroExtension.relativeRight (d.numeratorLayer R) (d.targetClass R) =
      SquareZeroExtension.relativeRight (d.denominatorLayer R) (d.sourceClass R) :=
  SquareZeroExtension.classModelMap_right _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
