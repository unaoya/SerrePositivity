module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRoofSource
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraExtensionBaseChangeMap

/-!
概要：元の二切断射を、元の左三角形で揃えた二つの実底変更模型の間に移す。
方針：元の postnikovMap と sourceLift・隣接遷移の自然性を同じ実 cospan 射に束ねる。
規約：元の上段射と両底射影の厳密な合成式を保持。使われ方：元の π₂ 射の比較。
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

lemma postnikovTwoRoofTransfer_base_square :
    c.sourceProjection ≫ postnikovMap R (f.app m).hom 1 = c.sourceLift ≫ c.roof.denominator :=
  c.source_denominator.symm

def postnikovTwoRoofTransfer : postnikovTwoRoofSource R f c ⟶ postnikovTwoRoofDenominator R f c :=
  ExtensionBaseChange.map R c.sourceProjection
    (postnikovTransition R (A.obj m).obj 2 1 (by omega)) c.roof.denominator
    (postnikovTransition R (B.obj m).obj 2 1 (by omega)) c.sourceLift
    (postnikovMap R (f.app m).hom 2) (postnikovMap R (f.app m).hom 1)
    (postnikovTwoRoofTransfer_base_square R f c)
    (postnikovTransition_naturality R (A.obj m).obj (f.app m).hom 2 1 (by omega)).symm

lemma postnikovTwoRoofTransfer_base :
    postnikovTwoRoofTransfer R f c ≫ postnikovTwoRoofDenominatorBase R f c =
      postnikovTwoRoofSourceBase R f c ≫ c.sourceLift :=
  ExtensionBaseChange.map_base R _ _ _ _ _ _ _ _ _

lemma postnikovTwoRoofTransfer_upper :
    postnikovTwoRoofTransfer R f c ≫ postnikovTwoRoofDenominatorUpper R f c =
      postnikovTwoRoofSourceUpper R f c ≫ postnikovMap R (f.app m).hom 2 :=
  ExtensionBaseChange.map_upper R _ _ _ _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
