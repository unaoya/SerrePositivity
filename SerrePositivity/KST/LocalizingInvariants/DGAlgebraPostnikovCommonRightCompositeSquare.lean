module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellFactorizationSquare
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightNaturalitySquare

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightCompositeSquare
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：元の A 遷移と fⱼ、fᵢ と B 遷移の合成自然性を、同じ共通底上で実際に比較する。
方針：元の分子を固定し、f の自然性で二因子分解を同じ合成射へそろえる。
規約：比較二重経路を追加入力しない。使われ方：Γ の右像貼合せへの実比較。
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

def postnikovCommonRightNaturalityComposite : (A.obj i).obj ⟶ (B.obj j).obj :=
  PostnikovCommonCore.postnikovCommonRightNaturalityComposite
    (R := R) (A := A) (B := B) (f := f) (i := i) (j := j) (hj := hj)

def postnikovCommonRightNaturalityCompositeLayer :
    Bimod (postnikovCommonClassBase R f c d) (postnikovCommonClassBase R f c d) :=
  PostnikovCommonCore.postnikovCommonRightNaturalityCompositeLayer
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightNaturalityCompositeSource : cellResolution R (cellResolution R
    (cellResolution R (cellResolution R (postnikovCommonClassBase R f c d)))) ⟶
    SquareZero.algebra (postnikovCommonClassBase R f c d)
      (postnikovCommonRightNaturalityCompositeLayer R f c d hj) :=
  PostnikovCommonCore.postnikovCommonRightNaturalityCompositeSource
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightNaturalityCompositeTarget : cellResolution R (cellResolution R
    (cellResolution R (cellResolution R (postnikovCommonClassBase R f c d)))) ⟶
    SquareZero.algebra (postnikovCommonClassBase R f c d)
      (postnikovCommonRightNaturalityCompositeLayer R f c d hj) :=
  PostnikovCommonCore.postnikovCommonRightNaturalityCompositeTarget
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightNaturalityViaA : SquareZero.RelativeWitness
    (postnikovCellFactorizationProjection R (postnikovCommonClassBase R f c d))
    (postnikovCommonRightNaturalityCompositeLayer R f c d hj)
    (postnikovCommonRightNaturalityCompositeSource R f c d hj)
    (postnikovCommonRightNaturalityCompositeTarget R f c d hj) :=
  PostnikovCommonCore.postnikovCommonRightNaturalityViaA
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightNaturalityViaB : SquareZero.RelativeWitness
    (postnikovCellFactorizationProjection R (postnikovCommonClassBase R f c d))
    (postnikovCommonRightNaturalityCompositeLayer R f c d hj)
    (postnikovCommonRightNaturalityCompositeSource R f c d hj)
    (postnikovCommonRightNaturalityCompositeTarget R f c d hj) :=
  PostnikovCommonCore.postnikovCommonRightNaturalityViaB
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightCompositeSquare : SquareZero.RelativeWitnessSquare
    (postnikovCommonRightNaturalityViaA R f c d hj)
    (postnikovCommonRightNaturalityViaB R f c d hj) :=
  PostnikovCommonCore.postnikovCommonRightCompositeSquare
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightCompositeTransportHomotopy : Path.Witness R
    (SquareZeroExtension.transport (postnikovCommonRightNaturalityCompositeLayer R f c d hj)
      (postnikovCommonRightNaturalityViaA R f c d hj))
    (SquareZeroExtension.transport (postnikovCommonRightNaturalityCompositeLayer R f c d hj)
      (postnikovCommonRightNaturalityViaB R f c d hj)) :=
  PostnikovCommonCore.postnikovCommonRightCompositeTransportHomotopy
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightCompositeTransportHomotopy_left :
    (postnikovCommonRightCompositeTransportHomotopy R f c d hj).hom ≫
      Path.map R (SquareZeroExtension.relativeLeft
        (postnikovCommonRightNaturalityCompositeLayer R f c d hj)
        (postnikovCommonRightNaturalityCompositeTarget R f c d hj)) =
    SquareZeroExtension.relativeLeft (postnikovCommonRightNaturalityCompositeLayer R f c d hj)
      (postnikovCommonRightNaturalityCompositeSource R f c d hj) ≫
      Path.diagonal R (cellResolution R (cellResolution R (cellResolution R
        (cellResolution R (postnikovCommonClassBase R f c d))))) :=
  PostnikovCommonCore.postnikovCommonRightCompositeTransportHomotopy_left
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightCompositeTransportHomotopy_right :
    (postnikovCommonRightCompositeTransportHomotopy R f c d hj).hom ≫
      Path.map R (SquareZeroExtension.relativeRight
        (postnikovCommonRightNaturalityCompositeLayer R f c d hj)
        (postnikovCommonRightNaturalityCompositeTarget R f c d hj)) =
    SquareZeroExtension.relativeRight (postnikovCommonRightNaturalityCompositeLayer R f c d hj)
      (postnikovCommonRightNaturalityCompositeSource R f c d hj) ≫
      Path.diagonal R (postnikovCommonClassBase R f c d) :=
  PostnikovCommonCore.postnikovCommonRightCompositeTransportHomotopy_right
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
