module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHomEvaluationWhisker
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHomPrecomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedPrecompositionNaturality

/-! # 閉細分の自由 Hom 評価の dg 関手自然性

概要：元の評価と細分後の評価の両方を、商側の自由係数へ厳密に比較する。
方針：評価の前後合成公式に、閉前合成の Hom 鎖写像の自然性を渡す。
規約：全次数の dg 関手等式。使われ方：細分 prism の商比較の両相。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D E : Type v) [DGCategory A D] [DGCategory A E]
variable [Small.{u} D] [Small.{u} E] (Q : DGFunctor A D E)

omit [Small.{u} D] [Small.{u} E] in
/-- 元の自由 Hom 評価は dg 関手像の係数変換を通じて商側の評価へ移る。 -/
lemma dgWalkingHomOriginalEvaluation_naturality (q y : D) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomOriginalEvaluation A D q y).comp Q =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomMap A (Q.map q y)).comp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomOriginalEvaluation A E (Q.obj q) (Q.obj y)) := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomEvaluation_postcomp A D E (homObject A D q y) q y (𝟙 _) Q).trans
    ((congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomEvaluation A E (homObject A D q y) (Q.obj q) (Q.obj y))
      ((Category.id_comp (Q.map q y)).trans (Category.comp_id (Q.map q y)).symm)).trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomMap_evaluation A E (Q.map q y) (Q.obj q) (Q.obj y) (𝟙 _)).symm)

/-- 細分後の自由 Hom 評価は、係数変換と閉細分の商像による評価へ移る。 -/
lemma dgWalkingHomRefinedEvaluation_naturality {p q : D} (y : D)
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomRefinedEvaluation A D y r).comp Q =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomMap A (Q.map q y)).comp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomRefinedEvaluation A E (Q.obj y) (Q.onClosed.map r)) := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomEvaluation_postcomp A D E (homObject A D q y) p y
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D r) Q).trans
      ((congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomEvaluation A E (homObject A D q y) (Q.obj p) (Q.obj y))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition_naturality A D E Q r)).trans
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomMap_evaluation A E (Q.map q y) (Q.obj p) (Q.obj y)
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A E (Q.onClosed.map r))).symm)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
