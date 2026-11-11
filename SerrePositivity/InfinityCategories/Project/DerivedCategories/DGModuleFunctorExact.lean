module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorConePreservation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleCofiberExists
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorZeroObjects
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberSquareComparisonIso

/-! # dg 加群間の dg 関手の完全性

概要：任意の dg 加群間の dg 関手の native nerve は完全である。
方針：標準 cone の保存を、同じ辺の cofiber 四角形の関手同型で全ての列へ移す。
規約：関手に追加の平坦性を要求しない。使われ方：β3 の Yoneda 模型による完全性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E] [Small.{u} E]
variable (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A (_root_.SerrePositivity.DifferentialGraded.RightModule A D) (_root_.SerrePositivity.DifferentialGraded.RightModule A E))

/-- 各実際の辺に、関手像も押し出しとなる cofiber 四角形を選べる。 -/
lemma dgModuleFunctor_cofiber_exists
    {x y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D)) x y) :
    ∃ s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare e, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (s.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) := by
  obtain ⟨M, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective x
  obtain ⟨N, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective y
  change ∃ s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D)
    (e : Truncated.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex M) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex N)), _
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge_edgeClosed A D e]
  exact ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberSquare A D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e),
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorConeSquare_isPushout A D E F (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed e)⟩

/-- dg 加群間の dg 関手は、選択によらず任意の実 cofiber 列を保つ。 -/
theorem dgModuleFunctorNerve_preservesCofiber (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve A D))
    (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence (t.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_preservesZeroVertices F)) := by
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ t.square))
  let s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare f := {
    toZeroTriangle := t
    bottom_edge := (SSet.yonedaEquiv.symm_apply_apply _).symm
    isPushout := ht }
  obtain ⟨r, hr⟩ := dgModuleFunctor_cofiber_exists A D E F f
  obtain ⟨e⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.nonempty_cofiberSquareFunctorIso r s
  exact hr.of_functorIso (e.postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F))

/-- 任意の dg 加群間の dg 関手の native nerve は完全である。 -/
theorem dgModuleFunctorNerve_isExactFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) where
  preservesZero := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_preservesZeroVertices F
  preservesCofiber := dgModuleFunctorNerve_preservesCofiber A D E F

end SerrePositivity.InfinityCategories.Project.DerivedCategories
