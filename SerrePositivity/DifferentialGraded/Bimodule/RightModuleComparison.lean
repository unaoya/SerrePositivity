module
public import SerrePositivity.DifferentialGraded.Bimodule.TensorModuleFull

/-! # 積dg圏のopposite上の右加群とbimoduleの比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

/-- 既存semifree解像度の圏から、全Hom自然な主bimodule圏への同値。 -/
def rightModuleBimoduleEquivalence :
    ModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ ≌ BimoduleCategory A B C :=
  (leftRightOppositeEquivalence A (DGTensorCategory A Bᵒᵖ C)).symm.trans
    (BimoduleTensorModule.equivalence A B C)

/-- 値の評価は元の右加群の積対象での評価と自然同型になる。 -/
def rightModuleBimoduleEvaluationIso (b : B) (c : C) :
    (rightModuleBimoduleEquivalence A B C).functor ⋙
        BimoduleCategory.valueEvaluation A B C b c ≅
      moduleEvaluation A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ (op (op b, c)) := by
  let E := leftRightOppositeEquivalence A (DGTensorCategory A Bᵒᵖ C)
  let V := moduleEvaluation A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ (op (op b, c))
  refine NatIso.ofComponents (fun M => V.mapIso (E.counitIso.app M)) ?_
  intro M N f
  change (BimoduleCategory.valueEvaluation A B C b c).map
      ((BimoduleTensorModule.functor A B C).map (E.inverse.map f)) ≫
        V.map (E.counitIso.app N).hom =
    V.map (E.counitIso.app M).hom ≫ V.map f
  rw [BimoduleTensorModule.functor_map_value]
  rw [← leftModuleToRightOpposite_map_eval A (DGTensorCategory A Bᵒᵖ C)]
  exact (V.map_comp _ _).symm.trans
    ((congrArg V.map (E.counitIso.hom.naturality f)).trans (V.map_comp _ _))

lemma rightModuleBimoduleEquivalence_quasiIso_iff
    {M N : ModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ} (f : M ⟶ N) :
    BimoduleCategory.quasiIso A B C ((rightModuleBimoduleEquivalence A B C).functor.map f) ↔
      moduleQuasiIso A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ f := by
  change BimoduleCategory.quasiIso A B C
    ((BimoduleTensorModule.functor A B C).map
      ((leftRightOppositeEquivalence A (DGTensorCategory A Bᵒᵖ C)).inverse.map f)) ↔ _
  rw [BimoduleTensorModule.functor_quasiIso_iff]
  let E := leftRightOppositeEquivalence A (DGTensorCategory A Bᵒᵖ C)
  let W := moduleQuasiIso A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
  change W (E.functor.map (E.inverse.map f)) ↔ W f
  calc
    W (E.functor.map (E.inverse.map f)) ↔
        W (E.functor.map (E.inverse.map f) ≫ (E.counitIso.app N).hom) :=
      (W.cancel_right_of_respectsIso _ _).symm
    _ ↔ W ((E.counitIso.app M).hom ≫ f) := by
      exact Iff.of_eq (congrArg (fun k => W k) (E.counitIso.hom.naturality f))
    _ ↔ W f := W.cancel_left_of_respectsIso _ _

end SerrePositivity.DifferentialGraded
