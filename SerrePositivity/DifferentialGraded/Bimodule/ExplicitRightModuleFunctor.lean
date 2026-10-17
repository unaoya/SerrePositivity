module
public import SerrePositivity.DifferentialGraded.Bimodule.UncurryClosedFunctor
public import SerrePositivity.DifferentialGraded.Bimodule.RightModuleComparison

/-! # bimoduleの積dg圏上の右加群への明示的関手と選択された逆関手の比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.BimoduleTensorModule
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]

def rightModuleFunctor : BimoduleCategory A B C ⥤
    ModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ :=
  uncurryFunctor A B C ⋙ leftModuleToRightOpposite A (DGTensorCategory A Bᵒᵖ C)

@[simp]
lemma rightModuleFunctor_map_value {M N : BimoduleCategory A B C} (f : M ⟶ N) (b : B) (c : C) :
    (moduleEvaluation A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ (op (op b, c))).map
        ((rightModuleFunctor A B C).map f) =
      (BimoduleCategory.valueEvaluation A B C b c).map f :=
  (leftModuleToRightOpposite_map_eval A (DGTensorCategory A Bᵒᵖ C)
    ((uncurryFunctor A B C).map f) (op b, c)).trans (uncurryMap_eval A B C f (op b, c))

/-- 明示的な右加群表示から既存の選択された戻り関手へ送ると元のbimoduleに戻る。 -/
def rightModuleCounitIso :
    rightModuleFunctor A B C ⋙ (rightModuleBimoduleEquivalence A B C).functor ≅
      𝟭 (BimoduleCategory A B C) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (uncurryFunctor A B C)
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (leftRightOppositeEquivalence A (DGTensorCategory A Bᵒᵖ C)).unitIso.symm
          (functor A B C) ≪≫ Functor.leftUnitor _) ≪≫ uncurryCounitIso A B C

/-- 明示的な右加群表示と、既存の圏同値が選択した逆関手との自然同型。 -/
def rightModuleInverseIso :
    rightModuleFunctor A B C ≅ (rightModuleBimoduleEquivalence A B C).inverse :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft (rightModuleFunctor A B C)
      (rightModuleBimoduleEquivalence A B C).unitIso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (rightModuleCounitIso A B C)
      (rightModuleBimoduleEquivalence A B C).inverse ≪≫ Functor.leftUnitor _

end SerrePositivity.DifferentialGraded.BimoduleTensorModule
