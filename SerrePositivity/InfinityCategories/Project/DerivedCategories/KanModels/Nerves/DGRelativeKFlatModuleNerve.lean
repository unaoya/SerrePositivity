module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.DGSemifreeModules
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.FullSubcomplexFibration
/-!
概要：右相対 K-flat dg 加群の実頂点全部分 ∞ 圏と、元の半自由模型の包含を構成する。
方針：全加群 nerve の頂点に元の K-flat 条件を課し、半自由加群の実 K-flat 性を使う。
規約：局所 Hom の平坦性を要求しない。使われ方：通常 tensor の実合成を導来化する入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 元の実 dg 加群頂点が持つ右相対 K-flat 条件。 -/
def dgModuleRelativeKFlatVertex (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R E) _⦋0⦌) : Prop :=
  moduleRelativeKFlat R E (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv x)
/-- 右相対 K-flat 加群の頂点全部分 ∞ 圏。 -/
abbrev dgRelativeKFlatModuleNerve :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R E) (dgModuleRelativeKFlatVertex R E) : SSet)
/-- 同じ実 K-flat 加群の全部分圏から全 dg 加群の nerve への包含。 -/
def dgRelativeKFlatModuleInclusion : dgRelativeKFlatModuleNerve R E ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R E :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleNerve R E) (dgModuleRelativeKFlatVertex R E)).ι
/-- 元の半自由包含の各頂点は、同じ加群の右相対 K-flat 条件を満たす。 -/
lemma dgSemifreeModuleInclusion_vertex_relativeKFlat
    (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R E) _⦋0⦌) :
    dgModuleRelativeKFlatVertex R E
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R E)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R E))).app (Opposite.op ⦋0⦌) x) := by
  obtain ⟨M, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv (A := R) (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R E)).symm.surjective x
  change _root_.SerrePositivity.DifferentialGraded.moduleRelativeKFlat R E M.val
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeModule_isRelativeKFlat R E M
/-- 半自由模型の同じ全単体包含を、右相対 K-flat 加群の全部分圏へ持ち上げる。 -/
def dgSemifreeToRelativeKFlatNerve :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R E ⟶ dgRelativeKFlatModuleNerve R E :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (dgModuleRelativeKFlatVertex R E)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R E)))
    (dgSemifreeModuleInclusion_vertex_relativeKFlat R E)
/-- K-flat 全部分圏への持ち上げは、元の指定半自由包含を厳密に回収する。 -/
lemma dgSemifreeToRelativeKFlatNerve_inclusion :
    dgSemifreeToRelativeKFlatNerve R E ≫ dgRelativeKFlatModuleInclusion R E =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R E)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleSemifreeProperty R E)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ (dgSemifreeModuleInclusion_vertex_relativeKFlat R E)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
