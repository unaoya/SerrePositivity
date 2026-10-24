module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightZeroGlue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightZeroBaseIso

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightClassGlue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：共通零標的で貼り合わせた経路を、元の共通底上の右 class 標的へ戻す。
方針：底変更の普遍性で両端を同定し、元の係数同型の逆で実経路を後合成する。
規約：元の二 class の右像と底への定数射影を保持。使われ方：次段の kernel 障害消去。
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
  (d : PostnikovCommonLayerInverse R f c)

def postnikovCommonRightGlueToCell : postnikovCommonRightZeroGlueSource R f c d ⟶
    cellResolution R (postnikovCommonClassBase R f c d) :=
  PostnikovCommonCore.postnikovCommonRightGlueToCell
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightGlueToCell_projection : postnikovCommonRightGlueToCell R f c d ≫
    cellAugmentation R (postnikovCommonClassBase R f c d) =
      postnikovCommonRightZeroGlueProjection R f c d :=
  PostnikovCommonCore.postnikovCommonRightGlueToCell_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

def postnikovCommonRightGlueTarget :=
  PostnikovCommonCore.postnikovCommonRightGlueTarget
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

def postnikovCommonRightGlueSource :=
  PostnikovCommonCore.postnikovCommonRightGlueSource
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightGlueTarget_projection : postnikovCommonRightGlueTarget R f c d ≫
    SquareZero.projection _ _ = postnikovCommonRightZeroGlueProjection R f c d :=
  PostnikovCommonCore.postnikovCommonRightGlueTarget_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightGlueSource_projection : postnikovCommonRightGlueSource R f c d ≫
    SquareZero.projection _ _ = postnikovCommonRightZeroGlueProjection R f c d :=
  PostnikovCommonCore.postnikovCommonRightGlueSource_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightZeroGlueLeft_eq : postnikovCommonRightZeroGlueLeft R f c d =
    postnikovCommonRightGlueTarget R f c d ≫ (postnikovCommonRightZeroBaseIso R f c d).hom :=
  PostnikovCommonCore.postnikovCommonRightZeroGlueLeft_eq
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightZeroGlueRight_eq : postnikovCommonRightZeroGlueRight R f c d =
    postnikovCommonRightGlueSource R f c d ≫ (postnikovCommonRightZeroBaseIso R f c d).hom :=
  PostnikovCommonCore.postnikovCommonRightZeroGlueRight_eq
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

/-- 元の二 class の右像を、同じ非正次数源と元の底に相対的な実経路で結ぶ。 -/
def postnikovCommonRightClassGlueWitness : Path.Witness R
    (postnikovCommonRightGlueTarget R f c d) (postnikovCommonRightGlueSource R f c d) :=
  PostnikovCommonCore.postnikovCommonRightClassGlueWitness
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightClassGlueWitness_projection :
    (postnikovCommonRightClassGlueWitness R f c d).hom ≫ Path.map R (SquareZero.projection _ _) =
      postnikovCommonRightZeroGlueProjection R f c d ≫
        Path.diagonal R (postnikovCommonClassBase R f c d) :=
  PostnikovCommonCore.postnikovCommonRightClassGlueWitness_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
