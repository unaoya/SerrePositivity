module
public import SerrePositivity.InfinityCategories.Derived.DGWalkingHomEvaluation
public import SerrePositivity.InfinityCategories.Derived.DGWalkingHomStrictNatTrans
public import SerrePositivity.InfinityCategories.Derived.DGClosedPrecompositionDirect
public import SerrePositivity.InfinityCategories.DGNerve.NatTrans

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 概要：元の Hom 複体の恒等評価。
方針：直接の閉前合成と自由 Hom の生成辺を使う。
規約：Small 仮定を加えず、全係数と指定時刻を保持する。
使われ方：一般対象宇宙の係数比較と既存版との一致。 -/
def dgWalkingHomOriginalEvaluationDirect (q y : D) :
    DGFunctor A (DGWalkingHom.{u, v} A (homObject A D q y)) D :=
  dgWalkingHomEvaluation A D (homObject A D q y) q y (𝟙 _)

/-- 概要：指定閉射による前合成で元の係数を評価する。
方針：直接の閉前合成と自由 Hom の生成辺を使う。
規約：Small 仮定を加えず、全係数と指定時刻を保持する。
使われ方：一般対象宇宙の係数比較と既存版との一致。 -/
def dgWalkingHomRefinedEvaluationDirect {p q : D} (y : D)
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q) :
    DGFunctor A (DGWalkingHom.{u, v} A (homObject A D q y)) D :=
  dgWalkingHomEvaluation A D (homObject A D q y) p y (dgClosedPrecompositionDirect A D r)

/-- 概要：始点では指定閉射、終点では恒等射を自然変換の成分にする。
方針：直接の閉前合成と自由 Hom の生成辺を使う。
規約：Small 仮定を加えず、全係数と指定時刻を保持する。
使われ方：一般対象宇宙の係数比較と既存版との一致。 -/
def dgWalkingHomPrecomposeComponentDirect {p q : D} (y : D)
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q) :
    ∀ x, zeroCycles (homObject A D
      ((dgWalkingHomRefinedEvaluationDirect A D y r).obj x)
      ((dgWalkingHomOriginalEvaluationDirect A D q y).obj x))
  | ⟨false⟩ => closedHomEquiv A D _ _ r
  | ⟨true⟩ => unitElement A y

/-- 概要：閉前合成から元の評価への全次数の厳密 dg 自然変換。
方針：直接の閉前合成と自由 Hom の生成辺を使う。
規約：Small 仮定を加えず、全係数と指定時刻を保持する。
使われ方：一般対象宇宙の係数比較と既存版との一致。 -/
def dgWalkingHomPrecomposeNatTransDirect {p q : D} (y : D)
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q) :
    StrictNatTrans (dgWalkingHomRefinedEvaluationDirect A D y r)
      (dgWalkingHomOriginalEvaluationDirect A D q y) := by
  apply dgWalkingHomStrictNatTrans A D (homObject A D q y)
    (dgWalkingHomRefinedEvaluationDirect A D y r) (dgWalkingHomOriginalEvaluationDirect A D q y)
    (dgWalkingHomPrecomposeComponentDirect A D y r)
  intro k a
  have hF := congrArg (fun f => f.f k a)
    (dgWalkingHomEvaluation_generator A D (homObject A D q y) p y
      (dgClosedPrecompositionDirect A D r))
  have hG := congrArg (fun f => f.f k a)
    (dgWalkingHomEvaluation_generator A D (homObject A D q y) q y (𝟙 _))
  change compose A (unitElement A y).val _ _ =
    compose A _ (closedHomEquiv A D _ _ r).val _
  change ((dgWalkingHomRefinedEvaluationDirect A D y r).map _ _).f k
    ((dgWalkingHomGenerator A (homObject A D q y)).f k a) =
      (dgClosedPrecompositionDirect A D r).f k a at hF
  change ((dgWalkingHomOriginalEvaluationDirect A D q y).map _ _).f k
    ((dgWalkingHomGenerator A (homObject A D q y)).f k a) = a at hG
  rw [hF, hG, unit_compose]
  exact dgClosedPrecompositionDirect_f A D r k a

end SerrePositivity.InfinityCategories
