module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHomEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHomStrictNatTrans
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedPrecompositionDirect
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NatTrans

/-!
概要：対象の Small 性なしに閉前合成の自由 Hom の厳密自然変換を構成する。
方針：直接構成した前合成鎖写像と、指定閉射・恒等射の成分を使う。
規約：元の対象・全次数・指定閉射を保持する。
使われ方：一般対象宇宙での全係数 prism と slice prism の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 概要：元の Hom 複体の恒等評価。
方針：直接の閉前合成と自由 Hom の生成辺を使う。
規約：Small 仮定を加えず、全係数と指定時刻を保持する。
使われ方：一般対象宇宙の係数比較と既存版との一致。 -/
def dgWalkingHomOriginalEvaluationDirect (q y : D) :
    DGFunctor A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHom.{u, v} A (homObject A D q y)) D :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomEvaluation A D (homObject A D q y) q y (𝟙 _)

/-- 概要：指定閉射による前合成で元の係数を評価する。
方針：直接の閉前合成と自由 Hom の生成辺を使う。
規約：Small 仮定を加えず、全係数と指定時刻を保持する。
使われ方：一般対象宇宙の係数比較と既存版との一致。 -/
def dgWalkingHomRefinedEvaluationDirect {p q : D} (y : D)
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q) :
    DGFunctor A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHom.{u, v} A (homObject A D q y)) D :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomEvaluation A D (homObject A D q y) p y (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecompositionDirect A D r)

/-- 概要：始点では指定閉射、終点では恒等射を自然変換の成分にする。
方針：直接の閉前合成と自由 Hom の生成辺を使う。
規約：Small 仮定を加えず、全係数と指定時刻を保持する。
使われ方：一般対象宇宙の係数比較と既存版との一致。 -/
def dgWalkingHomPrecomposeComponentDirect {p q : D} (y : D)
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q) :
    ∀ x, _root_.SerrePositivity.DifferentialGraded.zeroCycles (_root_.SerrePositivity.DifferentialGraded.homObject A D
      ((dgWalkingHomRefinedEvaluationDirect A D y r).obj x)
      ((dgWalkingHomOriginalEvaluationDirect A D q y).obj x))
  | ⟨false⟩ => _root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ r
  | ⟨true⟩ => _root_.SerrePositivity.DifferentialGraded.unitElement A y

/-- 概要：閉前合成から元の評価への全次数の厳密 dg 自然変換。
方針：直接の閉前合成と自由 Hom の生成辺を使う。
規約：Small 仮定を加えず、全係数と指定時刻を保持する。
使われ方：一般対象宇宙の係数比較と既存版との一致。 -/
def dgWalkingHomPrecomposeNatTransDirect {p q : D} (y : D)
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (dgWalkingHomRefinedEvaluationDirect A D y r)
      (dgWalkingHomOriginalEvaluationDirect A D q y) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomStrictNatTrans A D (homObject A D q y)
    (dgWalkingHomRefinedEvaluationDirect A D y r) (dgWalkingHomOriginalEvaluationDirect A D q y)
    (dgWalkingHomPrecomposeComponentDirect A D y r)
  intro k a
  have hF := congrArg (fun f => f.f k a)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomEvaluation_generator A D (homObject A D q y) p y
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecompositionDirect A D r))
  have hG := congrArg (fun f => f.f k a)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomEvaluation_generator A D (homObject A D q y) q y (𝟙 _))
  change _root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.unitElement A y).val _ _ =
    _root_.SerrePositivity.DifferentialGraded.compose A _ (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ r).val _
  change ((dgWalkingHomRefinedEvaluationDirect A D y r).map _ _).f k
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomGenerator A (homObject A D q y)).f k a) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecompositionDirect A D r).f k a at hF
  change ((dgWalkingHomOriginalEvaluationDirect A D q y).map _ _).f k
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomGenerator A (homObject A D q y)).f k a) = a at hG
  rw [hF, hG, _root_.SerrePositivity.DifferentialGraded.unit_compose]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecompositionDirect_f A D r k a

end SerrePositivity.InfinityCategories.Project.DerivedCategories
