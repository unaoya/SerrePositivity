module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGOverInitialRefinementInitialMaps
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInitialRefinementPositiveDegeneracies

/-! # over 閉始点細分と全正番号基本退化

概要：実 over 単体の全正番号基本退化は、同じ閉始点細分と厳密に可換となる。
方針：基本退化の零固定・正番号非零を、一般の順序写像の可換性へ渡す。
規約：apex 自身を繰り返す零番号退化は含めない。使われ方：図式の退化に対応する錐。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 全次元の実 over 細分は、任意の正番号基本退化と厳密に可換。 -/
lemma dgOverSimplexInitialRefinement_degeneracy_positive
    (a : Δ[0] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) {n : ℕ} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a) _⦋n⦌) (q : D)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
      ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceSimplex a σ)).obj 0))
    (j : Fin (n + 1)) (hj : j ≠ 0) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).σ j (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialRefinement A D a σ q s) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialRefinement A D a ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).σ j σ) q
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedTargetTransport A D s
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexReindex_source a (SimplexCategory.σ j) σ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgDegeneracy_zero j))) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgOverSimplexInitialRefinement_pullback_initial a (SimplexCategory.σ j) σ
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgDegeneracy_zero j) (fun i hi => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPositiveDegeneracy_ne_zero j hj i hi) q s

end SerrePositivity.InfinityCategories.Project.DerivedCategories
