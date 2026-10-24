module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassRetractBase
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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (lowerFunctor R n hn)) i m hi)
  (d : PostnikovCommonLayerInverse R hn f c) {j : ℕ} (hj : j ≤ i)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

abbrev postnikovCommonClassTransitionLayer :=
  bimoduleRestrict (postnikovCommonClassRetractBase R hn f c d (hj := hj))
    (postnikovShiftedLayerBimodule R (A.obj j).obj n hn 1)

def postnikovCommonClassTransitionCoefficient :
    roofShiftedNumeratorLayer R hn f
      (roofRefine R hn f c d.zero.source_le) 1 ⟶
        postnikovCommonClassTransitionLayer R hn f c d hj := postnikovCellClassOverCoefficient R
  (A.obj i).obj (A.obj j).obj (postnikovCommonClassBase R hn f c d) n hn
  (roofRefine R hn f c d.zero.source_le).roof.numerator (A.transition hj).hom

def postnikovCommonClassTransitionMap :
    SquareZero.algebra (postnikovCommonClassBase R hn f c d)
      (roofShiftedNumeratorLayer R hn f
        (roofRefine R hn f c d.zero.source_le) 1) ⟶
    SquareZero.algebra (postnikovCommonClassBase R hn f c d)
      (postnikovCommonClassTransitionLayer R hn f c d hj) := SquareZero.coefficientMap
  (postnikovCommonClassBase R hn f c d) (postnikovCommonClassTransitionCoefficient R hn f c d hj)

def postnikovCommonClassTransitionToZero :
    SquareZero.algebra (postnikovCommonClassBase R hn f c d)
      (postnikovCommonClassTransitionLayer R hn f c d hj) ⟶
    postnikovZeroClassTarget R (A.obj j).obj n 1 :=
  SquareZero.baseChangeMap (postnikovCommonClassRetractBase R hn f c d (hj := hj))
    (postnikovShiftedLayerBimodule R (A.obj j).obj n hn 1) ≫
      postnikovClassToZeroBase R (A.obj j).obj n hn 1

def postnikovCommonClassTransitionIso :
    SquareZero.algebra (postnikovCommonClassBase R hn f c d)
      (postnikovCommonClassTransitionLayer R hn f c d hj) ≅
    SquareZero.algebra (postnikovCommonClassBase R hn f c d)
      (bimoduleRestrict (postnikovCommonClassRetractBase R hn f c d (hj := hj) ≫
        postnikovTransition R (A.obj j).obj n 0 (by omega))
          (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (A.obj j).obj n) 1)) :=
  postnikovClassBaseZeroIso R (A.obj j).obj
  (postnikovCommonClassBase R hn f c d) n hn 1
    (postnikovCommonClassRetractBase R hn f c d (hj := hj))

lemma postnikovCommonClassTransitionToZero_projection :
    postnikovCommonClassTransitionToZero R hn f c d hj ≫ SquareZero.projection _ _ =
      SquareZero.projection _ _ ≫ (postnikovCommonClassRetractBase R hn f c d (hj := hj) ≫
        postnikovTransition R (A.obj j).obj n 0 (by omega)) := by
  rw [postnikovCommonClassTransitionToZero, Category.assoc, postnikovClassToZeroBase_projection,
    ← Category.assoc, SquareZero.baseChangeMap_projection, Category.assoc]

lemma postnikovCommonClassTransitionToZero_hom :
    (postnikovCommonClassTransitionToZero R hn f c d hj).hom =
      biprod.map ((postnikovCommonClassRetractBase R hn f c d (hj := hj)) ≫
        postnikovTransition R (A.obj j).obj n 0 (by omega)).hom
          (𝟙 ((postnikovLayer R (A.obj j).obj n)⟦(1 : ℤ)⟧)) := by
  change (SquareZero.baseChangeMap (postnikovCommonClassRetractBase R hn f c d (hj := hj))
    (postnikovShiftedLayerBimodule R (A.obj j).obj n hn 1)).hom ≫
      (postnikovClassToZeroBase R (A.obj j).obj n hn 1).hom = _
  rw [SquareZero.baseChangeMap_hom, postnikovClassToZeroBase_hom, cochainBiprodMap_comp]
  simp only [Category.id_comp]
  rfl

lemma postnikovCommonClassTransition_zero : postnikovCommonClassTransitionMap R hn f c d hj ≫
    postnikovCommonClassTransitionToZero R hn f c d hj = postnikovCommonNumeratorToZero R hn f c d ≫
      postnikovZeroClassMap R n 1 (A.transition hj).hom := by
  have hb : postnikovCommonClassRetractBase R hn f c d (hj := hj) ≫
      postnikovTransition R (A.obj j).obj n 0 (by omega) =
    (roofRefine R hn f c d.zero.source_le).roof.numerator ≫
      postnikovTransition R (A.obj i).obj n 0 (by omega) ≫
        postnikovMap R (A.transition hj).hom 0 := by
    rw [postnikovCommonClassRetractBase, Category.assoc, postnikovTransition_naturality]
  apply Mon.Hom.ext
  change (postnikovCommonClassTransitionMap R hn f c d hj).hom ≫
    (postnikovCommonClassTransitionToZero R hn f c d hj).hom =
      (postnikovCommonNumeratorToZero R hn f c d).hom ≫
        (postnikovZeroClassMap R n 1 (A.transition hj).hom).hom
  rw [postnikovCommonClassTransitionMap, SquareZero.coefficientMap_hom,
    postnikovCommonClassTransitionCoefficient, postnikovCellClassOverCoefficient_hom,
    postnikovCommonClassTransitionToZero_hom, congrArg Mon.Hom.hom hb,
    postnikovZeroClassMap_hom]
  change _ = ((SquareZero.baseChangeMap
    (roofRefine R hn f c d.zero.source_le).roof.numerator
    (postnikovShiftedLayerBimodule R (A.obj i).obj n hn 1)).hom ≫
      (postnikovClassToZeroBase R (A.obj i).obj n hn 1).hom) ≫ _
  rw [SquareZero.baseChangeMap_hom, postnikovClassToZeroBase_hom]
  let b := (roofRefine R hn f c d.zero.source_le).roof.numerator.hom
  let t := (postnikovTransition R (A.obj i).obj n 0 (by omega)).hom
  let v := (postnikovMap R (A.transition hj).hom 0).hom
  let u : (postnikovLayer R (A.obj i).obj n)⟦(1 : ℤ)⟧ ⟶
      (postnikovLayer R (A.obj j).obj n)⟦(1 : ℤ)⟧ :=
    (postnikovLayerMap R (A.transition hj).hom n)⟦(1 : ℤ)⟧'
  change biprod.map (𝟙 (postnikovCommonClassBase R hn f c d).X) u ≫
    biprod.map (b ≫ t ≫ v) (𝟙 _) =
      (biprod.map b (𝟙 ((postnikovLayer R (A.obj i).obj n)⟦(1 : ℤ)⟧)) ≫
        biprod.map t (𝟙 ((postnikovLayer R (A.obj i).obj n)⟦(1 : ℤ)⟧))) ≫ biprod.map v u
  apply biprod.hom_ext <;> simp [Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
