module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleFunctorCone
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleEvaluationIso

/-! # 任意 dg 加群値 dg 関手は実 cone を保つ

概要：写した射の cone と元の cone の像との実比較射は加群同型。
方針：各評価の複体値 dg 関手の既存同型を、全 dg 自然な比較射で照合する。
規約：平坦性・準同値性は不要。使われ方：実 cofiber 四角形の保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
variable (F : DGFunctor A (RightModule A D) (RightModule A E))
variable {M N : ModuleCategory A D}

/-- 実比較射は各評価で既存の非有界 cone 同型なので、加群同型である。 -/
instance dgModuleFunctorConeComparison_isIso (f : M ⟶ N) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorConeComparison A D E F f) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModule_isIso_of_evaluation
  intro x
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorConeComparison_eval]
  infer_instance

/-- 任意 dg 加群値 dg 関手による非有界 cone の実加群同型。 -/
def dgModuleFunctorConeIso (f : M ⟶ N) :
    moduleCone A E (F.onClosed.map f) ≅ F.onClosed.obj (moduleCone A D f) :=
  asIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorConeComparison A D E F f)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
