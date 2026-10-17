module
public import SerrePositivity.DifferentialGraded.Bimodule.RightRestrictionNaturality
public import SerrePositivity.DifferentialGraded.Tensor.RestrictionCylinder
public import SerrePositivity.DifferentialGraded.Tensor.BimoduleFunctor
public import SerrePositivity.DifferentialGraded.Derived.BimoduleBasic

/-! # 任意の前因子とのbimodule合成後のsource cylinder射影の準同型性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (E : Type z) [DGCategory A E] [Small.{u} E]

/-- 前因子を固定した、既存の合成双関手の通常関手への制限。 -/
def composeAfter (P : BimoduleCategory A B C) :
    BimoduleCategory A C E ⥤ BimoduleCategory A B E :=
  (((Functor.const (BimoduleCategory A C E)).obj P).prod'
    (𝟭 (BimoduleCategory A C E))) ⋙ composeFunctor A B C E

lemma rightTensor_bimoduleSourcePrecylinderProjection_quasiIso
    (M : ModuleCategory A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ)
    (L : LeftModule A C) (e : E) :
    QuasiIso ((BalancedTensor.rightTensorFunctor A C L).map
      ((BimoduleCategory.evaluation A C E e).map
        ((rightModuleBimoduleEquivalence A C E).functor.map
          (modulePrecylinder A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ M).π))) := by
  let T := BalancedTensor.rightTensorFunctor A C L
  let J := rightModuleBimoduleRightRestrictionNatIso A C E e
  let π := (modulePrecylinder A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ M).π
  have h := congrArg (fun k => T.map k) (J.hom.naturality π)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at h
  have : QuasiIso (T.map ((tensorRightRestriction A C E e).map π)) :=
    rightTensor_restrictedPrecylinderProjection_quasiIso A C (DGTensorCategory A Cᵒᵖ E)ᵒᵖ
      (tensorRightRestrictionInclusion A C E e) M L
  have hM : IsIso (J.hom.app M) := (J.app M).isIso_hom
  have hI : IsIso (J.hom.app
      (modulePrecylinder A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ M).I) := (J.app _).isIso_hom
  have hTM : IsIso (T.map (J.hom.app M)) := T.map_isIso (J.hom.app M)
  have hTI : IsIso (T.map (J.hom.app
      (modulePrecylinder A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ M).I)) := T.map_isIso _
  have hr : QuasiIso (T.map (J.hom.app
      (modulePrecylinder A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ M).I) ≫
        T.map ((tensorRightRestriction A C E e).map π)) := quasiIso_comp _ _
  have hl : QuasiIso
      (T.map (((rightModuleBimoduleEquivalence A C E).functor ⋙
        BimoduleCategory.evaluation A C E e).map π) ≫ T.map (J.hom.app M)) := h.symm ▸ hr
  exact quasiIso_of_comp_right
    (T.map (((rightModuleBimoduleEquivalence A C E).functor ⋙
      BimoduleCategory.evaluation A C E e).map π)) (T.map (J.hom.app M))

/-- 任意の前因子でも、積dg圏上の標準cylinder射影は合成後に準同型。 -/
lemma composeAfter_sourcePrecylinderProjection_quasiIso (P : BimoduleCategory A B C)
    (M : ModuleCategory A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ) :
    BimoduleCategory.quasiIso A B E ((composeAfter A B C E P).map
      ((rightModuleBimoduleEquivalence A C E).functor.map
        (modulePrecylinder A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ M).π)) := by
  intro b e
  change QuasiIso ((BimoduleCategory.valueEvaluation A B E b e).map
    (composeMap A B C E (𝟙 P) ((rightModuleBimoduleEquivalence A C E).functor.map
      (modulePrecylinder A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ M).π)))
  rw [composeMap_value_eval]
  change QuasiIso (BalancedTensor.map A C
    ((BimoduleCategory.evaluation A C E e).map ((rightModuleBimoduleEquivalence A C E).functor.map
      (modulePrecylinder A (DGTensorCategory A Cᵒᵖ E)ᵒᵖ M).π))
    ((BimoduleCategory.leftEvaluation A B C b).map (𝟙 P)))
  rw [CategoryTheory.Functor.map_id]
  exact rightTensor_bimoduleSourcePrecylinderProjection_quasiIso A C E M
    ((BimoduleCategory.underlying A B C P).leftAt b) e

end SerrePositivity.DifferentialGraded.BimoduleTensor
