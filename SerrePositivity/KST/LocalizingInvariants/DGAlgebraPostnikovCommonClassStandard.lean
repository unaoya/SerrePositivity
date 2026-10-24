module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassTransitionWitness

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassStandard
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：遷移した元の分子 class を、A の元の低い段の標準 class と実経路で比較する。
方針：既存の class 自然性経路を同じ cell 共通源へ移し、底の定数射影も回収する。
規約：同じ A の遷移と元の分子を保持。使われ方：二切断の実逆の class 整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

def postnikovCommonClassStandard : cellResolution R (postnikovCommonClassBase R f c d) ⟶
    SquareZero.algebra (postnikovCommonClassBase R f c d)
      (postnikovCommonClassTransitionLayer R f c d hj) :=
  PostnikovCommonCore.postnikovCommonClassStandard
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonClassStandardEndpoint :=
  PostnikovCommonCore.postnikovCommonClassStandardEndpoint
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

/-- 源は既存の右像貼合せと同じ非正次数代数。 -/
def postnikovCommonClassStandardWitness : Path.Witness R
    (postnikovCommonClassTransitionTarget R f c d (hj := hj))
    (postnikovCommonClassStandardEndpoint R f c d hj) :=
  PostnikovCommonCore.postnikovCommonClassStandardWitness
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonClassStandardEndpoint_projection :
    postnikovCommonClassStandardEndpoint R f c d hj ≫ SquareZero.projection _ _ =
      postnikovCommonRightZeroGlueProjection R f c d :=
  PostnikovCommonCore.postnikovCommonClassStandardEndpoint_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonClassStandardWitness_projection :
    (postnikovCommonClassStandardWitness R f c d hj).hom ≫ Path.map R (SquareZero.projection _ _) =
      postnikovCommonRightZeroGlueProjection R f c d ≫
        Path.diagonal R (postnikovCommonClassBase R f c d) :=
  PostnikovCommonCore.postnikovCommonClassStandardWitness_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
