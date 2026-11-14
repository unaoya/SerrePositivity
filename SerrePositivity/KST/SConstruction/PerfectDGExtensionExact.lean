module
public import SerrePositivity.KST.SConstruction.PerfectDGExtension
public import SerrePositivity.KST.SConstruction.DGModuleClosedExactInclusion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleFunctorExact

/-! # 実 Perf dg 延長の完全性
概要：厳密 dg 関手の実 Perf 延長の native nerve は完全である。
方針：元の包含との可換性から、周囲の cofiber 保存を充満 dg 部分圏へ反映する。
規約：任意の元の cofiber 列を保持する。使われ方：K-4d の S 構成上の射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E] [Small.{u} E]
  (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)

/-- 実 Perf dg 延長の nerve は、元の全 cofiber 列を保存する。 -/
lemma perfectDGExtensionNerve_isExactFunctor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension A D E F)) where
  preservesZero := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_preservesZeroVertices _
  preservesCofiber t ht := by
    let i := _root_.SerrePositivity.DifferentialGraded.perfectDGModuleInclusion A D Set.univ
    let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map i) :=
      dgModuleClosedInclusion_isExactFunctor A D _ (perfectDGClosedOperations A D Set.univ)
    let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorNerve_isExactFunctor A D E (dgModuleExtension A D E F)
    apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isColimitCone_of_fullInclusion A (RightModule A E)
      (modulePerfectProjectiveOver A E Set.univ) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone _)
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare ((t.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension A D E F)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGModuleInclusion A E Set.univ))
    rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, perfectDGExtension_inclusion, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp,
      ← Category.assoc]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber
      (t.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map i) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_preservesZeroVertices i))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber t ht)

/-- 元の厳密 dg 関手から得た実 Perf 延長を、K の安定入力間の射にする。 -/
def perfectDGStableMap : perfectDGStableModel A D Set.univ ⟶
    perfectDGStableModel A E Set.univ := by
  let := perfectDGExtensionNerve_isExactFunctor A D E F
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGExtension A D E F), preservesCofiberData_of_isExactFunctor _⟩

end SerrePositivity.KST.SConstruction
