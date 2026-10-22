module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRoofTransfer

/-!
概要：元の一切断逆の分子側の二切断拡大と、右経路の両端に沿う二つの実射を作る。
方針：元の fᵢ と B の遷移を通常底変更し、元の底射影・上段射を保持する。
規約：これらの実射の可逆性は未主張。使われ方：π₂ 逆の実代数への持ち上げ。
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

def postnikovTwoRoofNumerator : Mon (Complex R) :=
  postnikovExtensionBaseChange R (A.obj i).obj 1 c.roof.numerator

def postnikovTwoRoofRightFirst : c.roof.apex ⟶ postnikov R (B.obj i).obj 1 :=
  c.roof.numerator ≫ postnikovMap R (f.app i).hom 1

def postnikovTwoRoofRightSecond : c.roof.apex ⟶ postnikov R (B.obj i).obj 1 :=
  c.roof.denominator ≫ postnikovMap R (B.transition hi).hom 1

def postnikovTwoRoofRightWitness :
    Path.Witness R (postnikovTwoRoofRightFirst R f c) (postnikovTwoRoofRightSecond R f c) :=
  c.rightPath

def postnikovTwoRoofRightFirstModel : Mon (Complex R) :=
  postnikovExtensionBaseChange R (B.obj i).obj 1 (postnikovTwoRoofRightFirst R f c)

def postnikovTwoRoofRightSecondModel : Mon (Complex R) :=
  postnikovExtensionBaseChange R (B.obj i).obj 1 (postnikovTwoRoofRightSecond R f c)

def postnikovTwoRoofNumeratorMap :
    postnikovTwoRoofNumerator R f c ⟶ postnikovTwoRoofRightFirstModel R f c :=
  ExtensionBaseChange.map R c.roof.numerator
    (postnikovTransition R (A.obj i).obj 2 1 (by omega)) (postnikovTwoRoofRightFirst R f c)
    (postnikovTransition R (B.obj i).obj 2 1 (by omega)) (𝟙 c.roof.apex)
    (postnikovMap R (f.app i).hom 2) (postnikovMap R (f.app i).hom 1)
    (by rw [Category.id_comp]; rfl)
    (postnikovTransition_naturality R (A.obj i).obj (f.app i).hom 2 1 (by omega)).symm

def postnikovTwoRoofDenominatorMap :
    postnikovTwoRoofDenominator R f c ⟶ postnikovTwoRoofRightSecondModel R f c :=
  ExtensionBaseChange.map R c.roof.denominator
    (postnikovTransition R (B.obj m).obj 2 1 (by omega)) (postnikovTwoRoofRightSecond R f c)
    (postnikovTransition R (B.obj i).obj 2 1 (by omega)) (𝟙 c.roof.apex)
    (postnikovMap R (B.transition hi).hom 2) (postnikovMap R (B.transition hi).hom 1)
    (by rw [Category.id_comp]; rfl)
    (postnikovTransition_naturality R (B.obj m).obj (B.transition hi).hom 2 1 (by omega)).symm

lemma postnikovTwoRoofNumeratorMap_base : postnikovTwoRoofNumeratorMap R f c ≫
    postnikovExtensionBaseChangeBase R (B.obj i).obj 1 (postnikovTwoRoofRightFirst R f c) =
      postnikovExtensionBaseChangeBase R (A.obj i).obj 1 c.roof.numerator :=
  (ExtensionBaseChange.map_base R _ _ _ _ _ _ _ _ _).trans (Category.comp_id _)

lemma postnikovTwoRoofDenominatorMap_base : postnikovTwoRoofDenominatorMap R f c ≫
    postnikovExtensionBaseChangeBase R (B.obj i).obj 1 (postnikovTwoRoofRightSecond R f c) =
      postnikovTwoRoofDenominatorBase R f c :=
  (ExtensionBaseChange.map_base R _ _ _ _ _ _ _ _ _).trans (Category.comp_id _)

lemma postnikovTwoRoofNumeratorMap_upper : postnikovTwoRoofNumeratorMap R f c ≫
    postnikovExtensionBaseChangeUpper R (B.obj i).obj 1 (postnikovTwoRoofRightFirst R f c) =
      postnikovExtensionBaseChangeUpper R (A.obj i).obj 1 c.roof.numerator ≫
        postnikovMap R (f.app i).hom 2 := ExtensionBaseChange.map_upper R _ _ _ _ _ _ _ _ _

lemma postnikovTwoRoofDenominatorMap_upper : postnikovTwoRoofDenominatorMap R f c ≫
    postnikovExtensionBaseChangeUpper R (B.obj i).obj 1 (postnikovTwoRoofRightSecond R f c) =
      postnikovTwoRoofDenominatorUpper R f c ≫ postnikovMap R (B.transition hi).hom 2 :=
  ExtensionBaseChange.map_upper R _ _ _ _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
