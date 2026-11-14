module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ComplexSimplexArrow
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.StandardCofiberSquare

/-! # 任意の複体 dg nerve の span の表示

概要：任意の span を三複体と共通の始域を持つ二つの鎖写像で表示する。
方針：二辺の一単体から鎖写像を回収し、始域を等式で合わせる。
規約：HA Example 1.3.1.8。使われ方：指定された全ての span の標準 cofiber。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S]

/-- 始域を等式で同定した鎖写像は同じ一単体を定める。 -/
lemma complexEdge_eqToHom_comp {X Y Z : _root_.SerrePositivity.DifferentialGraded.Complex S} (h : X = Y) (f : Y ⟶ Z) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (eqToHom h ≫ f)).edge = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge f).edge := by
  cases h
  rw [eqToHom_refl, Category.id_comp]

/-- 三複体・二鎖写像による span の表示と元の図式との厳密な一致。 -/
structure ComplexSpanPresentation
    (p : (SSet.horn 2 0 : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) where
  sourceObj : _root_.SerrePositivity.DifferentialGraded.Complex S
  leftObj : _root_.SerrePositivity.DifferentialGraded.Complex S
  rightObj : _root_.SerrePositivity.DifferentialGraded.Complex S
  leftMap : sourceObj ⟶ leftObj
  rightMap : sourceObj ⟶ rightObj
  span_eq : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare leftMap rightMap) = p

/-- 任意の複体 dg nerve の span を通常の鎖写像で表示する。 -/
def presentComplexSpan
    (p : (SSet.horn 2 0 : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) :
    ComplexSpanPresentation p := by
  let s₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (Complex S) 1 := SSet.yonedaEquiv (SSet.horn₂₀.ι₀₁ ≫ p)
  let s₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (Complex S) 1 := SSet.yonedaEquiv (SSet.horn₂₀.ι₀₂ ≫ p)
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)).δ 1 s₀ = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)).δ 1 s₁ := by
    have H := congrArg (fun f => SSet.yonedaEquiv (f ≫ p)) SSet.horn₂₀.isPushout.w
    simpa only [Category.assoc, SSet.stdSimplex.yonedaEquiv_δ_comp] using H
  have hA : s₀.obj 0 = s₁.obj 0 :=
    congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex S (Complex S) 0 => s.obj 0) he
  refine ⟨s₀.obj 0, s₀.obj 1, s₁.obj 1, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexChainMap s₀,
    eqToHom hA ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplexChainMap s₁, ?_⟩
  apply SSet.horn₂₀.isPushout.hom_ext
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_bottomEdge,
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare_bottom, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge_simplexChainMap]
    exact SSet.yonedaEquiv.symm_apply_apply _
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_leftEdge,
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare_left, complexEdge_eqToHom_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge_simplexChainMap]
    exact SSet.yonedaEquiv.symm_apply_apply _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
