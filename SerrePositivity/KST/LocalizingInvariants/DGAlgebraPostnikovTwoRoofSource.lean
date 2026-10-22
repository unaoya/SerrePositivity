module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRoofDenominator

/-!
概要：元の左細分に沿って、元の二切断の始域拡大を非正次数の実代数に底変更する。
方針：元の sourceProjection の全射準同型性を、元の隣接遷移の通常 pullback で保つ。
規約：元の上段と底への実射影を保持。使われ方：元の二切断射の厳密な移送。
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

def postnikovTwoRoofSource : Mon (Complex R) :=
  postnikovExtensionBaseChange R (A.obj m).obj 1 c.sourceProjection

def postnikovTwoRoofSourceBase : postnikovTwoRoofSource R f c ⟶ c.source :=
  postnikovExtensionBaseChangeBase R (A.obj m).obj 1 c.sourceProjection

def postnikovTwoRoofSourceUpper : postnikovTwoRoofSource R f c ⟶ postnikov R (A.obj m).obj 2 :=
  postnikovExtensionBaseChangeUpper R (A.obj m).obj 1 c.sourceProjection

lemma postnikovTwoRoofSource_nonpositive : (postnikovTwoRoofSource R f c).X.IsStrictlyLE 0 := by
  have := c.source_nonpositive
  exact postnikovExtensionBaseChange_nonpositive R (A.obj m).obj 1 c.sourceProjection

lemma postnikovTwoRoofSourceUpper_epi : Epi (postnikovTwoRoofSourceUpper R f c).hom := by
  have := c.sourceProjection_epi
  exact postnikovExtensionBaseChangeUpper_epi R (A.obj m).obj 1 c.sourceProjection

lemma postnikovTwoRoofSourceUpper_quasiIso : QuasiIso (postnikovTwoRoofSourceUpper R f c).hom := by
  have := c.sourceProjection_epi
  exact postnikovExtensionBaseChangeUpper_quasiIso R (A.obj m).obj 1 c.sourceProjection
    c.sourceProjection_quasiIso

lemma postnikovTwoRoofSourceBase_connected : IsConnected R (postnikovTwoRoofSourceBase R f c) 2 :=
  postnikovExtensionBaseChangeBase_connected R (A.obj m).obj 1 c.sourceProjection

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
