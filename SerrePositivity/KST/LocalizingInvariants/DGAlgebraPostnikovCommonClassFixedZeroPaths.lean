module

public import
SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightFixedTransitionZeroProjection

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassFixedZeroPaths
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：fixed Γ の遷移・標準 class・互換性を同じ零底上の実相対経路へ移す。
方針：元の零底射の射影式を保つ底付き平方零代数射で移す。
規約：元の三経路の全射と端点を保持。使われ方：反転・合成の右像比較。
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

def postnikovCommonClassFixedZeroBase :=
  PostnikovCommonCore.postnikovCommonClassFixedZeroBase
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonClassFixedZeroMap :=
  PostnikovCommonCore.postnikovCommonClassFixedZeroMap
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonClassFixedZeroMap_projection :
    postnikovCommonClassFixedZeroMap R f c d hj ≫ SquareZero.projection _ _ =
      SquareZero.projection _ _ ≫ postnikovCommonClassFixedZeroBase R f c d hj :=
  PostnikovCommonCore.postnikovCommonClassFixedZeroMap_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

variable (e : PostnikovZeroLayerInverse R 1 f j i hj)

def postnikovCommonClassFixedTransitionMappedRelative :=
  PostnikovCommonCore.postnikovCommonClassFixedTransitionMappedRelative
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

def postnikovCommonClassFixedStandardMappedRelative :=
  PostnikovCommonCore.postnikovCommonClassFixedStandardMappedRelative
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonClassFixedCompatibilityMappedRelative :=
  PostnikovCommonCore.postnikovCommonClassFixedCompatibilityMappedRelative
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
