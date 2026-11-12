module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModulePropertyChoices
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModulePropertyStability
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExactFunctorChoice

/-! # 三角的対象条件を満たす dg 加群の包含の完全性

概要：K(D) の三角的対象条件による充満部分圏の native 包含は完全。
方針：各実辺で標準 cone 四角形を選び、その包含像が元の四角形であることを使う。
規約：任意の cofiber 列の保存を結論する。使われ方：前三角 dg 圏の Yoneda 埋め込み。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable (P : ObjectProperty (_root_.SerrePositivity.DifferentialGraded.ModuleHomotopyCategory A D))
variable [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]

/-- 各部分圏内の実辺には、周囲でも押し出しとなる cofiber 四角形がある。 -/
lemma dgModuleProperty_cofiber_exists_preserved
    {x y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePropertyNerve A D P) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePropertyNerve A D P)) x y) :
    ∃ s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare e, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare
      (s.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A (RightModule A D)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty A D P))) := by
  obtain ⟨M, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective x
  obtain ⟨N, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective y
  let a := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePropertyAmbientEdge A D P e
  let f := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed a
  let L := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePropertyConeSquare A D P f M.property N.property
  have he : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge A D f).edge = a.edge :=
    congrArg Truncated.Edge.edge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge_edgeClosed A D a)
  let s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare e := {
    square := L
    zero_corner := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift_zero_corner A _ _ _ _
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeZeroTriangle A D f).zero_corner
    bottom_edge := by
      apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift_edge A (RightModule A D)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty A D P) _ _ _ e
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_bottom]
      exact congrArg SSet.yonedaEquiv.symm he
    isPushout := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePropertyConeSquare_isPushout A D P f M.property N.property }
  refine ⟨s, ?_⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePropertyConeSquare A D P f M.property N.property ≫ _)
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePropertyConeSquare]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFullSquareLift_inclusion]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_isPushout A D f

/-- 三角的条件で閉じた全 dg 加群の充満部分圏の包含は完全。 -/
theorem dgModulePropertyInclusion_isExactFunctor :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A (RightModule A D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomotopyProperty A D P))) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_preserves_chosen_cofibers _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_preservesZeroVertices _) (dgModuleProperty_cofiber_exists_preserved A D P)

/-- 前三角 dg 圏のホモトピー表現可能部分から全加群への実包含は完全。 -/
theorem dgRepleteRepresentablesInclusion_isExactFunctor [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated A D] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion A (RightModule A D)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomotopyRepresentable A D))) :=
  dgModulePropertyInclusion_isExactFunctor A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty A D)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
