module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassFixedTransition
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoAffineClassCorrection
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessSourceChange

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedClassMap

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
    (d.classProjection R) (d.numeratorLayer R) (d.imageClass R) (d.targetClass R) :=
  PostnikovSuccessorClassInverseData.classFixedRelativeWitness
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma classFixedRelativeWitness_hom :
    (d.classFixedRelativeWitness R).hom =
    (postnikovCommonClassFixedGlueCompatibility R f d.baseInverse d.layerInverse
      d.inverse).hom :=
  PostnikovSuccessorClassInverseData.classFixedRelativeWitness_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def classFixedDefect : SquareZero.RelativeWitness (d.classProjection R) (d.numeratorLayer R)
    (d.targetClass R) (d.targetClass R) :=
  PostnikovSuccessorClassInverseData.classFixedDefect
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma classFixedDefect_correction :
    ((d.classRelativeWitness R).comp (d.classFixedDefect R)).hom =
      (d.classFixedRelativeWitness R).hom :=
  PostnikovSuccessorClassInverseData.classFixedDefect_correction
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def classFixedTargetCorrection : d.targetRelativeModel R ≅ d.targetRelativeModel R :=
  PostnikovSuccessorClassInverseData.classFixedTargetCorrection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def sourceToTargetFixedRelative : d.sourceRelativeModel R ⟶ d.targetRelativeModel R :=
  PostnikovSuccessorClassInverseData.sourceToTargetFixedRelative
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma sourceToTargetFixedRelative_correction : d.sourceToTargetRelative R ≫
    (d.classFixedTargetCorrection R).hom = d.sourceToTargetFixedRelative R :=
  PostnikovSuccessorClassInverseData.sourceToTargetFixedRelative_correction
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma sourceToTargetFixedRelative_left : d.sourceToTargetFixedRelative R ≫
    SquareZeroExtension.relativeLeft (d.numeratorLayer R) (d.targetClass R) =
      SquareZeroExtension.relativeLeft (d.denominatorLayer R) (d.sourceClass R) :=
  PostnikovSuccessorClassInverseData.sourceToTargetFixedRelative_left
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma sourceToTargetFixedRelative_right : d.sourceToTargetFixedRelative R ≫
    SquareZeroExtension.relativeRight (d.numeratorLayer R) (d.targetClass R) =
      SquareZeroExtension.relativeRight (d.denominatorLayer R) (d.sourceClass R) :=
  PostnikovSuccessorClassInverseData.sourceToTargetFixedRelative_right
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
