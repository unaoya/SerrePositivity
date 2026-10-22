module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightClassGlue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroClassMap

/-!
概要：共通右 class 標的への射を、元の A の零 class 標的と f の像で因子分解する。
方針：零底の自然性と元の係数射を、実代数射の二つの対角成分で照合する。
規約：元の分子射と shift 係数を保持。使われ方：後続段の実係数逆で右像を外す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c)

lemma postnikovCommonRightZeroBase_source : postnikovCommonRightZeroBase R f c d =
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator ≫
      postnikovTransition R (A.obj i).obj 1 0 (by omega) ≫ postnikovMap R (f.app i).hom 0 := by
  rw [postnikovCommonRightZeroBase_num, postnikovCommonRightBase, Category.assoc,
    postnikovTransition_naturality]

def postnikovCommonNumeratorToZero :
    SquareZero.algebra (postnikovCommonClassBase R f c d)
      (postnikovOneRoofShiftedNumeratorLayer R f
        (postnikovOneRoofRefine R f c d.zero.source_le) 1) ⟶
      postnikovZeroClassTarget R (A.obj i).obj 1 1 :=
  SquareZero.baseChangeMap (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator
    (postnikovShiftedLayerBimodule R (A.obj i).obj 1 (by omega) 1) ≫
      postnikovClassToZeroBase R (A.obj i).obj 1 (by omega) 1

lemma postnikovCommonRightNumerator_zero : postnikovCommonRightClassNumeratorMap R f c d ≫
    postnikovCommonRightClassToZero R f c d =
      postnikovCommonNumeratorToZero R f c d ≫ postnikovZeroClassMap R 1 1 (f.app i).hom := by
  apply Mon.Hom.ext
  change (postnikovCommonRightClassNumeratorMap R f c d).hom ≫
    (postnikovCommonRightClassToZero R f c d).hom =
      (postnikovCommonNumeratorToZero R f c d).hom ≫
        (postnikovZeroClassMap R 1 1 (f.app i).hom).hom
  rw [postnikovCommonRightClassNumeratorMap, SquareZero.coefficientMap_hom,
    postnikovCommonRightShiftedNumeratorMap_hom, postnikovCommonRightClassToZero_hom,
    postnikovZeroClassMap_hom]
  change _ = ((SquareZero.baseChangeMap
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator
    (postnikovShiftedLayerBimodule R (A.obj i).obj 1 (by omega) 1)).hom ≫
      (postnikovClassToZeroBase R (A.obj i).obj 1 (by omega) 1).hom) ≫ _
  rw [SquareZero.baseChangeMap_hom, postnikovClassToZeroBase_hom,
    congrArg Mon.Hom.hom (postnikovCommonRightZeroBase_source R f c d)]
  let b := (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator.hom
  let t := (postnikovTransition R (A.obj i).obj 1 0 (by omega)).hom
  let v := (postnikovMap R (f.app i).hom 0).hom
  let u : (postnikovLayer R (A.obj i).obj 1)⟦(1 : ℤ)⟧ ⟶
      (postnikovLayer R (B.obj i).obj 1)⟦(1 : ℤ)⟧ :=
    (postnikovLayerMap R (f.app i).hom 1)⟦(1 : ℤ)⟧'
  change biprod.map (𝟙 (postnikovCommonClassBase R f c d).X) u ≫
    biprod.map (b ≫ t ≫ v) (𝟙 _) =
      (biprod.map b (𝟙 ((postnikovLayer R (A.obj i).obj 1)⟦(1 : ℤ)⟧)) ≫
        biprod.map t (𝟙 ((postnikovLayer R (A.obj i).obj 1)⟦(1 : ℤ)⟧))) ≫ biprod.map v u
  apply biprod.hom_ext <;> simp [Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
