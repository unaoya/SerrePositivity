module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.LinearHomCohomology
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGStandardClosedPrecomposition
/-!
概要：標準豊穣後合成を元の閉射の全 Hom 鎖写像へ同定する。
方針：閉定数との AW 合成を各斉次成分で照合する。
規約：全単体で厳密に一致し、小ささの仮定を追加しない。
使われ方：coslice の線形係数作用をコホモロジーチャートの自然性へ渡す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]

lemma dgBarCompactStandardSimplicialPostcomp_chainMap {x y z : D}
    (f : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) z) :
    eHomWhiskerLeft SSet (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x) f =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactStandardModuleMap
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition R D (x := x) f)) := by
  ext n s
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) y z).map
    (SimplexCategory.const ⦋n.unop.len⦌ ⦋0⦌ 0).op
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedStandardVertexEquiv (R := R) (D := D) y z f)) s = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStandardClosedConstant_eq]
  apply Subtype.ext
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant (closedHomEquiv R D y z f) _).val s.val).component
    J k hJ hk = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStandardSimplexMap _ s).val.component J k hJ hk
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.awData_closed_post_component, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStandardSimplexMap_component]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition_f R D (x := x) f k (s.val.component J k hJ hk)).symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
