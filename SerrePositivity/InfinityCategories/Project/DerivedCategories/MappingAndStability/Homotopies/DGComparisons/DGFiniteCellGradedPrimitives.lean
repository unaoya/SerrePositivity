module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.LocalizationAndRoofs.DGFiniteCellTargetDenominator
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleClosedRightShift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleRightShiftBoundaries
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGRepresentableDerivedPrimitives

/-! # 有限 cell 加群標的の斉次閉元の実分母後の原始元

概要：表現可能加群から有限 cell 標的への任意次数の閉元を、元の閉分母で境界にする。
方針：標的シフトへの閉射を導来零化し、始域の射影性から具体的な原始元を回収する。
規約：商と K-flat 性は不要。使われ方：最後外ホーンの加群 cone 残差の消去。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 表現可能始域の全 Hom 元に、元の閉射の Yoneda 像を前合成する。 -/
def dgRepresentableModulePrecompose {q x : D} {M : _root_.SerrePositivity.DifferentialGraded.RightModule A D} (n : ℤ)
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom A (_root_.SerrePositivity.DifferentialGraded.representable A x) M n)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) :
    _root_.SerrePositivity.DifferentialGraded.GradedHom A (_root_.SerrePositivity.DifferentialGraded.representable A q) M n :=
  _root_.SerrePositivity.DifferentialGraded.compose A f (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A (_root_.SerrePositivity.DifferentialGraded.RightModule A D) _ _
    ((_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).onClosed.map s)).val (zero_add n)

variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D]

/-- 指定有限 cell 標的の斉次閉元は、元の実閉分母の前合成後に具体的な境界になる。 -/
theorem dgFiniteCellGraded_exists_closedPrimitive (P : Set D) (x : D)
    (M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D)
    (hM : _root_.SerrePositivity.DifferentialGraded.derivedFiniteCellOver A D P ((_root_.SerrePositivity.DifferentialGraded.moduleToDerived A D).obj M))
    (n k : ℤ) (hkn : k + 1 = n)
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom A (_root_.SerrePositivity.DifferentialGraded.representable A x) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M) n)
    (hf : _root_.SerrePositivity.DifferentialGraded.differential A f = 0) :
    ∃ (q : D) (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x),
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A D s).edge ∈ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierEdges A D P ∧
        ∃ h : _root_.SerrePositivity.DifferentialGraded.GradedHom A (_root_.SerrePositivity.DifferentialGraded.representable A q) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M) k,
          (_root_.SerrePositivity.DifferentialGraded.moduleHom A D (_root_.SerrePositivity.DifferentialGraded.representable A q) (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M)).d k n h =
            dgRepresentableModulePrecompose A D n f s := by
  let F := _root_.SerrePositivity.DifferentialGraded.moduleToDerived A D
  let c := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClosedRightShift A D n f hf
  have hshift : _root_.SerrePositivity.DifferentialGraded.derivedFiniteCellOver A D P (F.obj (M⟦n⟧)) :=
    (_root_.SerrePositivity.DifferentialGraded.derivedFiniteCellOver A D P).prop_of_iso ((F.commShiftIso n).app M).symm
      ((_root_.SerrePositivity.DifferentialGraded.derivedFiniteCellOver A D P).le_shift n _ hM)
  obtain ⟨q, s, hs, hz⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFiniteCellTarget_exists_closedDenominator A D P x hshift (F.map c)
  let t := (_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).onClosed.map s
  have hz' : F.map (t ≫ c) = 0 := by
    rw [Functor.map_comp]
    exact hz
  obtain ⟨b, hb⟩ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveDerived_zero_iff_primitive A D
    (_root_.SerrePositivity.DifferentialGraded.representable_homotopicallyProjective A D q) (t ≫ c)).mp hz'
  refine ⟨q, s, hs, ?_⟩
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomRightShift_exists_primitive_iff A D n k hkn
    (dgRepresentableModulePrecompose A D n f s)).mp
  exact ⟨b, hb.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClosedRightShift_precompose_cycle A D n f hf t)⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
