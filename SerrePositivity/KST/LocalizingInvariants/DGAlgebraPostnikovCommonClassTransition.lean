module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassRetractBase
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellClassOverImage
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassBaseZeroIso

/-!
概要：遷移後の元の底の class 標的と、元の A の層遷移の係数射を構成する。
方針：元の class の底変更係数を使い、零底自然性を対角直和の二成分で照合する。
規約：元の分子・遷移と係数を保持。使われ方：底変更で戻した経路の両端同定。
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
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

abbrev postnikovCommonClassTransitionLayer :=
  bimoduleRestrict (postnikovCommonClassRetractBase R f c d (hj := hj))
    (postnikovShiftedLayerBimodule R (A.obj j).obj 1 (by omega) 1)

def postnikovCommonClassTransitionCoefficient :
    postnikovOneRoofShiftedNumeratorLayer R f
      (postnikovOneRoofRefine R f c d.zero.source_le) 1 ⟶
        postnikovCommonClassTransitionLayer R f c d hj := postnikovCellClassOverCoefficient R
  (A.obj i).obj (A.obj j).obj (postnikovCommonClassBase R f c d) 1 (by omega)
  (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator (A.transition hj).hom

def postnikovCommonClassTransitionMap :
    SquareZero.algebra (postnikovCommonClassBase R f c d)
      (postnikovOneRoofShiftedNumeratorLayer R f
        (postnikovOneRoofRefine R f c d.zero.source_le) 1) ⟶
    SquareZero.algebra (postnikovCommonClassBase R f c d)
      (postnikovCommonClassTransitionLayer R f c d hj) := SquareZero.coefficientMap
  (postnikovCommonClassBase R f c d) (postnikovCommonClassTransitionCoefficient R f c d hj)

def postnikovCommonClassTransitionToZero :
    SquareZero.algebra (postnikovCommonClassBase R f c d)
      (postnikovCommonClassTransitionLayer R f c d hj) ⟶
    postnikovZeroClassTarget R (A.obj j).obj 1 1 :=
  SquareZero.baseChangeMap (postnikovCommonClassRetractBase R f c d (hj := hj))
    (postnikovShiftedLayerBimodule R (A.obj j).obj 1 (by omega) 1) ≫
      postnikovClassToZeroBase R (A.obj j).obj 1 (by omega) 1

def postnikovCommonClassTransitionIso :
    SquareZero.algebra (postnikovCommonClassBase R f c d)
      (postnikovCommonClassTransitionLayer R f c d hj) ≅
    SquareZero.algebra (postnikovCommonClassBase R f c d)
      (bimoduleRestrict (postnikovCommonClassRetractBase R f c d (hj := hj) ≫
        postnikovTransition R (A.obj j).obj 1 0 (by omega))
          (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (A.obj j).obj 1) 1)) :=
  postnikovClassBaseZeroIso R (A.obj j).obj
  (postnikovCommonClassBase R f c d) 1 (by omega) 1
    (postnikovCommonClassRetractBase R f c d (hj := hj))

lemma postnikovCommonClassTransitionToZero_projection :
    postnikovCommonClassTransitionToZero R f c d hj ≫ SquareZero.projection _ _ =
      SquareZero.projection _ _ ≫ (postnikovCommonClassRetractBase R f c d (hj := hj) ≫
        postnikovTransition R (A.obj j).obj 1 0 (by omega)) := by
  rw [postnikovCommonClassTransitionToZero, Category.assoc, postnikovClassToZeroBase_projection,
    ← Category.assoc, SquareZero.baseChangeMap_projection, Category.assoc]

lemma postnikovCommonClassTransitionToZero_hom :
    (postnikovCommonClassTransitionToZero R f c d hj).hom =
      biprod.map ((postnikovCommonClassRetractBase R f c d (hj := hj)) ≫
        postnikovTransition R (A.obj j).obj 1 0 (by omega)).hom
          (𝟙 ((postnikovLayer R (A.obj j).obj 1)⟦(1 : ℤ)⟧)) := by
  change (SquareZero.baseChangeMap (postnikovCommonClassRetractBase R f c d (hj := hj))
    (postnikovShiftedLayerBimodule R (A.obj j).obj 1 (by omega) 1)).hom ≫
      (postnikovClassToZeroBase R (A.obj j).obj 1 (by omega) 1).hom = _
  rw [SquareZero.baseChangeMap_hom, postnikovClassToZeroBase_hom, cochainBiprodMap_comp]
  simp only [Category.id_comp]
  rfl

lemma postnikovCommonClassTransition_zero : postnikovCommonClassTransitionMap R f c d hj ≫
    postnikovCommonClassTransitionToZero R f c d hj = postnikovCommonNumeratorToZero R f c d ≫
      postnikovZeroClassMap R 1 1 (A.transition hj).hom := by
  have hb : postnikovCommonClassRetractBase R f c d (hj := hj) ≫
      postnikovTransition R (A.obj j).obj 1 0 (by omega) =
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator ≫
      postnikovTransition R (A.obj i).obj 1 0 (by omega) ≫
        postnikovMap R (A.transition hj).hom 0 := by
    rw [postnikovCommonClassRetractBase, Category.assoc, postnikovTransition_naturality]
  apply Mon.Hom.ext
  change (postnikovCommonClassTransitionMap R f c d hj).hom ≫
    (postnikovCommonClassTransitionToZero R f c d hj).hom =
      (postnikovCommonNumeratorToZero R f c d).hom ≫
        (postnikovZeroClassMap R 1 1 (A.transition hj).hom).hom
  rw [postnikovCommonClassTransitionMap, SquareZero.coefficientMap_hom,
    postnikovCommonClassTransitionCoefficient, postnikovCellClassOverCoefficient_hom,
    postnikovCommonClassTransitionToZero_hom, congrArg Mon.Hom.hom hb,
    postnikovZeroClassMap_hom]
  change _ = ((SquareZero.baseChangeMap
    (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator
    (postnikovShiftedLayerBimodule R (A.obj i).obj 1 (by omega) 1)).hom ≫
      (postnikovClassToZeroBase R (A.obj i).obj 1 (by omega) 1).hom) ≫ _
  rw [SquareZero.baseChangeMap_hom, postnikovClassToZeroBase_hom]
  let b := (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator.hom
  let t := (postnikovTransition R (A.obj i).obj 1 0 (by omega)).hom
  let v := (postnikovMap R (A.transition hj).hom 0).hom
  let u : (postnikovLayer R (A.obj i).obj 1)⟦(1 : ℤ)⟧ ⟶
      (postnikovLayer R (A.obj j).obj 1)⟦(1 : ℤ)⟧ :=
    (postnikovLayerMap R (A.transition hj).hom 1)⟦(1 : ℤ)⟧'
  change biprod.map (𝟙 (postnikovCommonClassBase R f c d).X) u ≫
    biprod.map (b ≫ t ≫ v) (𝟙 _) =
      (biprod.map b (𝟙 ((postnikovLayer R (A.obj i).obj 1)⟦(1 : ℤ)⟧)) ≫
        biprod.map t (𝟙 ((postnikovLayer R (A.obj i).obj 1)⟦(1 : ℤ)⟧))) ≫ biprod.map v u
  apply biprod.hom_ext <;> simp [Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
