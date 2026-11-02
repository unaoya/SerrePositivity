module
public import SerrePositivity.KST.SConstruction.DGTensorLeftUnitAssociativity
public import SerrePositivity.DifferentialGraded.SharedFunctoriality.DGModuleExtensionInputTransport
public import SerrePositivity.KST.SConstruction.DGFunctorGraphRightUnit

/-! # 元の実延長の右恒等入力と tensor 左単位
概要：右恒等入力の元の合成比較を、出力側の同じ実単位と照合する。
方針：graph の単位回収と、元の左単位・逆結合の両立を等号移送つきで合成する。
規約：大きい加群型の smallness は要求しない。使われ方：実 Perf の右単位法則。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

section Generic
variable (B : Type v) (C : Type w) [DGCategory A B] [Small.{u} B] [DGCategory A C]

/-- 対角との等号を保つ、任意の元の双加群の左単位同型。 -/
def dgBimoduleDiagonalUnitIso (R : Bimodule A B B) (h : R = Bimodule.diagonal A B)
    (P : Bimodule A B C) :
    BimoduleCategory.of A B C (BimoduleTensor.compose A B B C R P) ≅
      BimoduleCategory.of A B C P :=
  eqToIso (congrArg (fun S => BimoduleCategory.of A B C
    (BimoduleTensor.compose A B B C S P)) h) ≪≫ BimoduleTensor.leftBimoduleUnitIso A B C P

end Generic

variable (D : Type v) (E : Type w)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]

/-- 左端の対角等号を含めて、元の左単位と逆結合は両立する。 -/
lemma dgBimoduleDiagonalUnit_associator (R : Bimodule A E E)
    (h : R = Bimodule.diagonal A E) (P : Bimodule A E D) :
    (BimoduleTensor.associatorIso A E E D (RightModule A D) R P (DGFunctor.id _)).inv ≫
        (dgModuleGraphTensorFunctor A D E).map
          (dgBimoduleDiagonalUnitIso A E D R h P).hom =
      (dgBimoduleDiagonalUnitIso A E (RightModule A D) R h
        (BimoduleTensor.compose A E D (RightModule A D) P (DGFunctor.id _))).hom := by
  subst R
  simp only [dgBimoduleDiagonalUnitIso, eqToIso_refl, Iso.refl_trans]
  change (BimoduleTensor.associatorIso A E E D (RightModule A D)
      (Bimodule.diagonal A E) P (DGFunctor.id _)).inv ≫
      BimoduleTensor.composeMap A E D (RightModule A D)
        (BimoduleTensor.leftBimoduleUnitIso A E D P).hom
        (𝟙 (BimoduleCategory.of A D (RightModule A D) (DGFunctor.id _))) = _
  exact dgTensorLeftUnit_associator_inv A E D (RightModule A D) P (DGFunctor.id _)

/-- 元の右恒等入力の合成比較は、出力の同じ tensor 左単位を回収する。 -/
lemma dgModuleExtensionCompositionTensorIso_comp_id (F : DGFunctor A D E) :
    (dgModuleExtensionCompositionTensorIso A D E E F (DGFunctor.id E)).hom ≫
        (dgModuleGraphTensorFunctor A D E).map
          (dgFunctorGraphInputIso A D E (strictDGFunctor_comp_id F)).hom =
      (dgBimoduleDiagonalUnitIso A E (RightModule A D)
        (functorGraph A E E (DGFunctor.id E)) (functorGraph_identity A E)
        (dgModuleExtension A D E F)).hom := by
  simp only [dgModuleExtensionCompositionTensorIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc]
  rw [← Functor.map_comp]
  have h := congrArg (fun e => (dgModuleGraphTensorFunctor A D E).map e.hom)
    (dgFunctorGraphCompositionIso_comp_id A D E F)
  simp only [Iso.trans_hom] at h
  rw [h]
  exact dgBimoduleDiagonalUnit_associator A D E _ (functorGraph_identity A E)
    (functorGraph A D E F)

/-- 出力の tensor 単位の評価は、同じ実延長の対象における以前の単位比較。 -/
lemma dgBimoduleDiagonalUnitIso_extension_evaluation (R : Bimodule A E E)
    (h : R = Bimodule.diagonal A E) (F : DGFunctor A D E) (M : RightModule A D) :
    (BimoduleCategory.evaluation A E (RightModule A D) M).mapIso
        (dgBimoduleDiagonalUnitIso A E (RightModule A D) R h (dgModuleExtension A D E F)) =
      dgDiagonalTensorUnitAt A E R h ((dgModuleExtension A D E F).obj M) := by
  subst R
  simp only [dgBimoduleDiagonalUnitIso, eqToIso_refl, Iso.refl_trans]
  rfl

end SerrePositivity.KST.SConstruction
