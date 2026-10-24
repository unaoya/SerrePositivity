module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeRightRoofSource
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovFiniteNonpositiveDiagonal

/-!
概要：元の有限切断右逆の左欠損を、指定全経路を持つ非正次数対角模型への射に束ねる。
方針：元の二射と f の先の実経路を cospan lift に渡し、cover へ一意に持ち上げる。
規約：欠損経路を定数経路に取り替えない。使われ方：対角右逆による左経路の反映。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision HomotopyPullbackModel
variable (R : Type u) [CommRing R] (cutoff : ℤ) {A B : Tower (NonpositiveAlgebra R)}
  (f : LevelHom A B) {m k : ℕ} {hmk : m ≤ k}
  (c : NativeRightInverseRoof R (f.map (postnikovFunctor R cutoff)) m k hmk)

local instance finiteDefectSource_nonpositive : (c.nonpositiveSource R).X.IsStrictlyLE 0 :=
  coverComplex_nonpositive R (cellResolution R (postnikov R (A.obj k).obj cutoff))

local instance finiteDefectOriginalSource_nonpositive :
    ((A.map (postnikovFunctor R cutoff)).obj k).X.IsStrictlyLE 0 :=
  postnikov_nonpositive R (A.obj k).obj cutoff

def postnikovFiniteDefectPair : c.nonpositiveSource R ⟶
    ((postnikovFiniteDiagonalTarget R cutoff f).obj m).obj :=
  connectiveCoverLift R (lift R (postnikovMap R (f.app m).hom cutoff)
    (postnikovMap R (f.app m).hom cutoff) (c.sourceLift R ≫ c.roof.numerator)
    (c.sourceProjection R ≫ postnikovMap R (A.transition hmk).hom cutoff)
    (c.sourceDefectAfterF R))

lemma postnikovFiniteDefectPair_left : postnikovFiniteDefectPair R cutoff f c ≫
    postnikovFiniteDiagonalLeft R cutoff f m = c.sourceLift R ≫ c.roof.numerator := by
  rw [postnikovFiniteDefectPair, postnikovFiniteDiagonalLeft, ← Category.assoc,
    connectiveCoverLift_inclusion, lift_left]

lemma postnikovFiniteDefectPair_right : postnikovFiniteDefectPair R cutoff f c ≫
    postnikovFiniteDiagonalRight R cutoff f m =
      c.sourceProjection R ≫ postnikovMap R (A.transition hmk).hom cutoff := by
  rw [postnikovFiniteDefectPair, postnikovFiniteDiagonalRight, ← Category.assoc,
    connectiveCoverLift_inclusion, lift_right]

lemma postnikovFiniteDefectPair_path : postnikovFiniteDefectPair R cutoff f c ≫
    connectiveCoverInclusion R ((postnikovFiniteDiagonalRawTarget R cutoff f).obj m) ≫
      path R (postnikovMap R (f.app m).hom cutoff) (postnikovMap R (f.app m).hom cutoff) =
    (c.sourceDefectAfterF R).hom := by
  rw [postnikovFiniteDefectPair, ← Category.assoc, connectiveCoverLift_inclusion, lift_path]

variable {i : ℕ} (him : i ≤ m)

lemma postnikovFiniteDiagonalLeft_naturality :
    ((postnikovFiniteDiagonalTarget R cutoff f).transition him).hom ≫ postnikovFiniteDiagonalLeft R cutoff f i =
      postnikovFiniteDiagonalLeft R cutoff f m ≫ postnikovMap R (A.transition him).hom cutoff :=
  ((coverTowerCounit R (postnikovFiniteDiagonalRawTarget R cutoff f)).comp
    (leftProjection R (f.map (postnikovFunctor R cutoff))
      (f.map (postnikovFunctor R cutoff)))).naturality him

lemma postnikovFiniteDiagonalRight_naturality :
    ((postnikovFiniteDiagonalTarget R cutoff f).transition him).hom ≫ postnikovFiniteDiagonalRight R cutoff f i =
      postnikovFiniteDiagonalRight R cutoff f m ≫ postnikovMap R (A.transition him).hom cutoff :=
  ((coverTowerCounit R (postnikovFiniteDiagonalRawTarget R cutoff f)).comp
    (rightProjection R (f.map (postnikovFunctor R cutoff))
      (f.map (postnikovFunctor R cutoff)))).naturality him

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
