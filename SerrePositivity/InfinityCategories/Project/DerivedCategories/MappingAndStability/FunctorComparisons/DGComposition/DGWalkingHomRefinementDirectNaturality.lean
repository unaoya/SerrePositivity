module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGWalkingHomEvaluationWhisker
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGWalkingHomPrecompositionDirect
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGClosedPrecompositionDirect

/-!
概要：自由 Hom の元の評価と直接前合成評価の自然性を示す。
方針：直接の閉前合成鎖写像と全二相単体の係数比較を使う。
規約：始域・標的の Small 仮定なしに、元の対象と全係数を保持する。
使われ方：D2 の一般対象宇宙での dg gluing 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D E : Type v) [DGCategory A D] [DGCategory A E]
variable (Q : DGFunctor A D E)

/-- 概要：元の自由 Hom 評価は dg 関手像の係数変換を通じて商側の評価へ移る。
方針：直接の閉前合成と自由 Hom の生成辺を使う。
規約：Small 仮定を加えず、全係数と指定時刻を保持する。
使われ方：一般対象宇宙の係数比較と既存版との一致。 -/
lemma dgWalkingHomOriginalEvaluationDirect_naturality (q y : D) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomOriginalEvaluationDirect A D q y).comp Q =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomMap A (Q.map q y)).comp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomOriginalEvaluationDirect A E (Q.obj q) (Q.obj y)) := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomEvaluation_postcomp A D E (homObject A D q y) q y (𝟙 _) Q).trans
    ((congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomEvaluation A E (homObject A D q y) (Q.obj q) (Q.obj y))
      ((Category.id_comp (Q.map q y)).trans (Category.comp_id (Q.map q y)).symm)).trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomMap_evaluation A E (Q.map q y) (Q.obj q) (Q.obj y) (𝟙 _)).symm)

/-- 概要：細分後の自由 Hom 評価は、係数変換と閉細分の商像による評価へ移る。
方針：直接の閉前合成と自由 Hom の生成辺を使う。
規約：Small 仮定を加えず、全係数と指定時刻を保持する。
使われ方：一般対象宇宙の係数比較と既存版との一致。 -/
lemma dgWalkingHomRefinedEvaluationDirect_naturality {p q : D} (y : D)
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomRefinedEvaluationDirect A D y r).comp Q =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomMap A (Q.map q y)).comp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomRefinedEvaluationDirect A E (Q.obj y) (Q.onClosed.map r)) := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomEvaluation_postcomp A D E (homObject A D q y) p y
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecompositionDirect A D r) Q).trans
      ((congrArg (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomEvaluation A E (homObject A D q y) (Q.obj p) (Q.obj y))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecompositionDirect_naturality A D E Q r)).trans
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomMap_evaluation A E (Q.map q y) (Q.obj p) (Q.obj y)
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecompositionDirect A E (Q.onClosed.map r))).symm)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
