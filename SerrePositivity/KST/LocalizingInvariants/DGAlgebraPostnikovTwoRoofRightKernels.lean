module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRoofNumerator
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovBaseChangedKernelHomologyNaturality

/-!
概要：分子側と分母側の二切断射の kernel 射を、元の H⁻² の射へ同定する。
方針：同じ底射の厳密な正方形を、実 kernel と指定ホモロジー同型の自然性へ渡す。
規約：係数逆の実代数への持ち上げは未主張。使われ方：元の π₂ の eventual 逆との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)

def postnikovTwoRoofNumeratorKernelMap :
    kernel (postnikovExtensionBaseChangeBase R (A.obj i).obj 1 c.roof.numerator).hom ⟶
      kernel (postnikovExtensionBaseChangeBase R (B.obj i).obj 1
        (postnikovTwoRoofRightFirst R f c)).hom :=
  postnikovBaseChangedKernelMap R (f.app i).hom 1 c.roof.numerator
    (postnikovTwoRoofRightFirst R f c) (𝟙 c.roof.apex) (by rw [Category.id_comp]; rfl)

def postnikovTwoRoofDenominatorKernelMap :
    kernel (postnikovTwoRoofDenominatorBase R f c).hom ⟶
      kernel (postnikovExtensionBaseChangeBase R (B.obj i).obj 1
        (postnikovTwoRoofRightSecond R f c)).hom :=
  postnikovBaseChangedKernelMap R (B.transition hi).hom 1 c.roof.denominator
    (postnikovTwoRoofRightSecond R f c) (𝟙 c.roof.apex) (by rw [Category.id_comp]; rfl)

lemma postnikovTwoRoofNumeratorKernelMap_inclusion :
    postnikovTwoRoofNumeratorKernelMap R f c ≫
      kernel.ι (postnikovExtensionBaseChangeBase R (B.obj i).obj 1
        (postnikovTwoRoofRightFirst R f c)).hom =
    kernel.ι (postnikovExtensionBaseChangeBase R (A.obj i).obj 1 c.roof.numerator).hom ≫
      (postnikovTwoRoofNumeratorMap R f c).hom :=
  postnikovBaseChangedKernelMap_inclusion R _ _ _ _ _ _

lemma postnikovTwoRoofDenominatorKernelMap_inclusion :
    postnikovTwoRoofDenominatorKernelMap R f c ≫
      kernel.ι (postnikovExtensionBaseChangeBase R (B.obj i).obj 1
        (postnikovTwoRoofRightSecond R f c)).hom =
    kernel.ι (postnikovTwoRoofDenominatorBase R f c).hom ≫
      (postnikovTwoRoofDenominatorMap R f c).hom :=
  postnikovBaseChangedKernelMap_inclusion R _ _ _ _ _ _

lemma postnikovTwoRoofNumeratorKernelMap_original :
    homologyMap (postnikovTwoRoofNumeratorKernelMap R f c) (-2) ≫
      (postnikovBaseChangedKernelHomologyIso R (B.obj i).obj 1
        (postnikovTwoRoofRightFirst R f c)).hom =
    (postnikovBaseChangedKernelHomologyIso R (A.obj i).obj 1 c.roof.numerator).hom ≫
      homologyMap (f.app i).hom.hom (-2) :=
  postnikovBaseChangedKernelHomologyIso_naturality R _ _ _ _ _ _

lemma postnikovTwoRoofDenominatorKernelMap_original :
    homologyMap (postnikovTwoRoofDenominatorKernelMap R f c) (-2) ≫
      (postnikovBaseChangedKernelHomologyIso R (B.obj i).obj 1
        (postnikovTwoRoofRightSecond R f c)).hom =
    (postnikovTwoRoofDenominatorKernelHomologyIso R f c).hom ≫
      homologyMap (B.transition hi).hom.hom (-2) :=
  postnikovBaseChangedKernelHomologyIso_naturality R _ _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
