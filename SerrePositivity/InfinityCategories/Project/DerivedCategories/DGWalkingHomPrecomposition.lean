module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHomEvaluation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHomStrictNatTrans
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedPrecompositionChainMap
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NatTrans

/-! # 閉前合成を実現する自由係数の厳密 dg 自然変換

概要：閉前合成した評価から元の評価への厳密 dg 自然変換を構成する。
方針：始点の成分を指定閉射、終点の成分を恒等射とし、生成辺上で合成を照合する。
規約：全斉次射に対する自然性を証明する。使われ方：実屋根の全次数の細分 prism。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 元の Hom 複体の恒等評価。 -/
def dgWalkingHomOriginalEvaluation (q y : D) :
    DGFunctor A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHom.{u, v} A (homObject A D q y)) D :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomEvaluation A D (homObject A D q y) q y (𝟙 _)

/-- 指定閉射による前合成で元の係数を評価する。 -/
def dgWalkingHomRefinedEvaluation {p q : D} (y : D)
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q) :
    DGFunctor A (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGWalkingHom.{u, v} A (homObject A D q y)) D :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomEvaluation A D (homObject A D q y) p y (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D r)

/-- 始点では指定閉射、終点では恒等射を自然変換の成分にする。 -/
def dgWalkingHomPrecomposeComponent {p q : D} (y : D)
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q) :
    ∀ x, _root_.SerrePositivity.DifferentialGraded.zeroCycles (_root_.SerrePositivity.DifferentialGraded.homObject A D
      ((dgWalkingHomRefinedEvaluation A D y r).obj x)
      ((dgWalkingHomOriginalEvaluation A D q y).obj x))
  | ⟨false⟩ => _root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ r
  | ⟨true⟩ => _root_.SerrePositivity.DifferentialGraded.unitElement A y

/-- 閉前合成から元の評価への全次数の厳密 dg 自然変換。 -/
def dgWalkingHomPrecomposeNatTrans {p q : D} (y : D)
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (dgWalkingHomRefinedEvaluation A D y r)
      (dgWalkingHomOriginalEvaluation A D q y) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomStrictNatTrans A D (homObject A D q y)
    (dgWalkingHomRefinedEvaluation A D y r) (dgWalkingHomOriginalEvaluation A D q y)
    (dgWalkingHomPrecomposeComponent A D y r)
  intro k a
  have hF := congrArg (fun f => f.f k a)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomEvaluation_generator A D (homObject A D q y) p y
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D r))
  have hG := congrArg (fun f => f.f k a)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomEvaluation_generator A D (homObject A D q y) q y (𝟙 _))
  change _root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.unitElement A y).val _ _ =
    _root_.SerrePositivity.DifferentialGraded.compose A _ (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ r).val _
  change ((dgWalkingHomRefinedEvaluation A D y r).map _ _).f k
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomGenerator A (homObject A D q y)).f k a) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D r).f k a at hF
  change ((dgWalkingHomOriginalEvaluation A D q y).map _ _).f k
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgWalkingHomGenerator A (homObject A D q y)).f k a) = a at hG
  rw [hF, hG, _root_.SerrePositivity.DifferentialGraded.unit_compose]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition_f A D r k a

end SerrePositivity.InfinityCategories.Project.DerivedCategories
