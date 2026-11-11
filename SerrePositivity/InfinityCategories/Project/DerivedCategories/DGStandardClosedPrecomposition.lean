module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStandardClosedPostcomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStandardHomChainMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ClosedPrecompositionComponents
/-!
概要：標準 DK の豊穣前合成を、同じ全 Hom 鎖写像の全単体作用へ同定する。
方針：閉定数の AW 成分式と豊穣前合成の次数別式を照合する。
規約：対象圏の Small 性を仮定しない。
使われ方：D-8 c5 の余積包含による実 Hom の積の検査。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]

lemma dgStandardClosedConstant_eq {x y : D}
    (f : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y).map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedStandardVertexEquiv (R := R) (D := D) x y f) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv R D x y f) n := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStandardSimplicialPostcomp_app R D x x y f n (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnit x n)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y).map
    (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedStandardVertexEquiv (R := R) (D := D) x y f)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnit x n) = _ at h
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW_unit_right] using h

lemma dgStandardSimplicialPrecomp_chainMap {x y z : D}
    (f : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) x ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) y) :
    eHomWhiskerRight SSet f (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) z) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStandardHomChainMap.dgStandardHomChainMap
        (eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) f (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) z)) := by
  ext n s
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW s ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y).map
    (SimplexCategory.const ⦋n.unop.len⦌ ⦋0⦌ 0).op
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedStandardVertexEquiv (R := R) (D := D) x y f)) = _
  rw [dgStandardClosedConstant_eq]
  apply Subtype.ext
  funext i
  rcases i with ⟨⟨L, k⟩, hL, hk⟩
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData s.val (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant (closedHomEquiv R D x y f) _).val).component
    L k hL hk = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStandardSimplexMap _ s).val.component L k hL hk
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.awData_closed_pre_component, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStandardSimplexMap_component]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomWhiskerRight_f R D (x := x) (y := y) (z := z) f k
    (s.val.component L k hL hk)).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
