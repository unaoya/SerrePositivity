module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightFixedClassGlue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassAffine

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassFixedTransition
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：指定右経路の貼合せから、元の係数逆と標準 class に沿う新 class 互換性を作る。
方針：既存の後続段の係数逆と底変更同型を使い、標準 class 経路と同じ源上で合成する。
規約：元の両端・係数・共通底を保持。使われ方：整合する Γ 模型射の再構成。
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
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} {hj : j ≤ i}
  (e : PostnikovZeroLayerInverse R 1 f j i hj)

def postnikovCommonClassFixedRetractWitness : Path.Witness R
    (postnikovCommonClassRetractTarget R f c d (hj := hj))
    (postnikovCommonClassRetractSource R f c d (hj := hj)) :=
  PostnikovCommonCore.postnikovCommonClassFixedRetractWitness
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

lemma postnikovCommonClassFixedRetractWitness_projection :
    (postnikovCommonClassFixedRetractWitness R f c d e).hom ≫
      Path.map R (SquareZero.projection _ _) =
    postnikovCommonRightZeroGlueProjection R f c d ≫
      (postnikovCommonRightZeroBase R f c d ≫ e.base) ≫
        Path.diagonal R (postnikov R (A.obj j).obj 0) :=
  PostnikovCommonCore.postnikovCommonClassFixedRetractWitness_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

def postnikovCommonClassFixedRetractRelativeWitness : Path.Witness R
    (postnikovCommonClassRetractLeft R f c d e) (postnikovCommonClassRetractRight R f c d e) :=
  PostnikovCommonCore.postnikovCommonClassFixedRetractRelativeWitness
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

lemma postnikovCommonClassFixedRetractRelativeWitness_projection :
    (postnikovCommonClassFixedRetractRelativeWitness R f c d e).hom ≫
      Path.map R (SquareZero.projection _ _) = postnikovCommonRightZeroGlueProjection R f c d ≫
        Path.diagonal R (postnikovCommonClassBase R f c d) :=
  PostnikovCommonCore.postnikovCommonClassFixedRetractRelativeWitness_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

def postnikovCommonClassFixedTransitionWitness : Path.Witness R
    (postnikovCommonClassTransitionTarget R f c d (hj := hj))
    (postnikovCommonClassTransitionSource R f c d (hj := hj)) :=
  PostnikovCommonCore.postnikovCommonClassFixedTransitionWitness
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

lemma postnikovCommonClassFixedTransitionWitness_projection :
    (postnikovCommonClassFixedTransitionWitness R f c d e).hom ≫
      Path.map R (SquareZero.projection _ _) = postnikovCommonRightZeroGlueProjection R f c d ≫
        Path.diagonal R (postnikovCommonClassBase R f c d) :=
  PostnikovCommonCore.postnikovCommonClassFixedTransitionWitness_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

def postnikovCommonClassFixedTransitionRelative : SquareZero.RelativeWitness
    (postnikovCommonRightZeroGlueProjection R f c d)
    (postnikovCommonClassTransitionLayer R f c d hj)
    (postnikovCommonClassTransitionTarget R f c d (hj := hj))
    (postnikovCommonClassTransitionSource R f c d (hj := hj)) :=
  PostnikovCommonCore.postnikovCommonClassFixedTransitionRelative
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

def postnikovCommonClassFixedCompatibility : SquareZero.RelativeWitness
    (postnikovCommonRightZeroGlueProjection R f c d)
    (postnikovCommonClassTransitionLayer R f c d hj)
    (postnikovCommonClassTransitionSource R f c d (hj := hj))
    (postnikovCommonClassStandardEndpoint R f c d hj) :=
  PostnikovCommonCore.postnikovCommonClassFixedCompatibility
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

def postnikovCommonClassFixedGlueCompatibility : SquareZero.RelativeWitness
    (postnikovCommonClassStandardGlueProjection R f c d)
    (postnikovCommonClassTransitionLayer R f c d hj)
    (postnikovCommonClassStandardGlueLeft R f c d (hj := hj))
    (postnikovCommonClassStandardGlueRight R f c d (hj := hj)) :=
  PostnikovCommonCore.postnikovCommonClassFixedGlueCompatibility
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj) (e := e)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
