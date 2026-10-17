module
public import SerrePositivity.DifferentialGraded.Morita.PerfectQuasiEquivalence
public import SerrePositivity.DifferentialGraded.Derived.BimoduleRestrictionEquivalence

/-! # U16b：積dg圏の擬同値と局所Hom条件を保持したPerf制限

既存の導来bimodule制限の条件hC・hDを保ち、積のHomのtensorが無条件に擬同型とはしない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (F : DGFunctor A B D) (G : DGFunctor A C E)
  (hF : QuasiEquivalence F) (hG : QuasiEquivalence G)
  (hC : localHomKFlat A C) (hD : localHomKFlat A D)

def quasiEquivalenceProductPerfectRestrictionEquivalence :
    PerfectModuleCategory A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ ≌
      PerfectModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ :=
  (quasiEquivalencePerfectEquivalence A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
    (DGTensorCategory A Dᵒᵖ E)ᵒᵖ (F.op.tensor G).op
    (bimoduleRestrictionDG_quasiEquivalence A B C D E F G hF hG hC hD)).symm

def quasiEquivalenceProductPerfectRestrictionSquare :
    (quasiEquivalenceProductPerfectRestrictionEquivalence A B C D E F G hF hG hC hD).functor ⋙
        perfectModuleInclusion A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ Set.univ ≅
      perfectModuleInclusion A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ Set.univ ⋙
        bimoduleRestrictionModuleDerived A B C D E F G :=
  quasiEquivalencePerfectRestrictionInclusionIso A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
    (DGTensorCategory A Dᵒᵖ E)ᵒᵖ (F.op.tensor G).op
    (bimoduleRestrictionDG_quasiEquivalence A B C D E F G hF hG hC hD)

end SerrePositivity.DifferentialGraded
