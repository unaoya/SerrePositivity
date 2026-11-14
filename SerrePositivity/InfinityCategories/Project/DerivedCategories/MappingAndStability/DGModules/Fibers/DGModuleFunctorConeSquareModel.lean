module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleConeSquareData
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleSquareFunctor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleSquarePostcomposeIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleFunctorConeComponents
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Fibers.DGModuleConePushout

/-! # cone の実同型による関手像の四角形模型

概要：写した射の標準 cofiber 四角形を cone 同型で後合成し、実押し出し模型を得る。
方針：四角形全体の関手同型で普遍性を運び、下側の実二単体を関手像と照合する。
規約：零角の変更は別途必要。使われ方：dg 加群関手の cofiber 保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory A E] [Small.{u} E]
variable (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A (_root_.SerrePositivity.DifferentialGraded.RightModule A D) (_root_.SerrePositivity.DifferentialGraded.RightModule A E))
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- 元の cone の実像を終点に持つ標準 cofiber 四角形模型。 -/
def dgModuleFunctorConeSquareModel (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleSquareData A E (F.onClosed.obj M) (F.onClosed.obj N)
      (_root_.SerrePositivity.DifferentialGraded.moduleZero A E) (F.onClosed.obj (_root_.SerrePositivity.DifferentialGraded.moduleCone A D f)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquareData A E (F.onClosed.map f)).postcompose
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorConeComparison A D E F f)

/-- 模型は標準 cone 四角形全体との実関手同型を持つ。 -/
def dgModuleFunctorConeSquareModelFunctorIso (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A E (F.onClosed.map f))
      (dgModuleFunctorConeSquareModel A D E F f).square := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquareData_square]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquareData A E (F.onClosed.map f)).postcomposeFunctorIso _

/-- 実関手同型で運んだ模型は実押し出し四角形である。 -/
lemma dgModuleFunctorConeSquareModel_isPushout (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (dgModuleFunctorConeSquareModel A D E F f).square :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_isPushout A E (F.onClosed.map f)).of_functorIso
    (dgModuleFunctorConeSquareModelFunctorIso A D E F f)

/-- 模型の下側の実二単体は元の標準四角形の関手像と等しい。 -/
lemma dgModuleFunctorConeSquareModel_lower (f : M ⟶ N) :
    (dgModuleFunctorConeSquareModel A D E F f).lowerTriangle =
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquareData A D f).map F).lowerTriangle := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplex2_ext
  · rfl
  · rfl
  · apply heq_of_eq
    exact congrArg (fun g => (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A) g)).val)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorConeComparison_inr A D E F f)
  · apply heq_of_eq
    change (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A)
      ((0 : F.onClosed.obj M ⟶ _root_.SerrePositivity.DifferentialGraded.moduleCone A E (F.onClosed.map f)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorConeComparison A D E F f))).val =
      (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A)
        (F.onClosed.map (0 : M ⟶ _root_.SerrePositivity.DifferentialGraded.moduleCone A D f)))).val
    rw [zero_comp, Functor.map_zero]
  · exact heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorConeComparison_inl A D E F f)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
