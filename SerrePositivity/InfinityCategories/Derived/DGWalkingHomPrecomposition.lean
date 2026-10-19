module
public import SerrePositivity.InfinityCategories.Derived.DGWalkingHomEvaluation
public import SerrePositivity.InfinityCategories.Derived.DGWalkingHomStrictNatTrans
public import SerrePositivity.InfinityCategories.Derived.DGClosedPrecompositionChainMap
public import SerrePositivity.InfinityCategories.DGNerve.NatTrans

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 元の Hom 複体の恒等評価。 -/
def dgWalkingHomOriginalEvaluation (q y : D) :
    DGFunctor A (DGWalkingHom.{u, v} A (homObject A D q y)) D :=
  dgWalkingHomEvaluation A D (homObject A D q y) q y (𝟙 _)

/-- 指定閉射による前合成で元の係数を評価する。 -/
def dgWalkingHomRefinedEvaluation {p q : D} (y : D)
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q) :
    DGFunctor A (DGWalkingHom.{u, v} A (homObject A D q y)) D :=
  dgWalkingHomEvaluation A D (homObject A D q y) p y (dgClosedPrecomposition A D r)

/-- 始点では指定閉射、終点では恒等射を自然変換の成分にする。 -/
def dgWalkingHomPrecomposeComponent {p q : D} (y : D)
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q) :
    ∀ x, zeroCycles (homObject A D
      ((dgWalkingHomRefinedEvaluation A D y r).obj x)
      ((dgWalkingHomOriginalEvaluation A D q y).obj x))
  | ⟨false⟩ => closedHomEquiv A D _ _ r
  | ⟨true⟩ => unitElement A y

/-- 閉前合成から元の評価への全次数の厳密 dg 自然変換。 -/
def dgWalkingHomPrecomposeNatTrans {p q : D} (y : D)
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q) :
    StrictNatTrans (dgWalkingHomRefinedEvaluation A D y r)
      (dgWalkingHomOriginalEvaluation A D q y) := by
  apply dgWalkingHomStrictNatTrans A D (homObject A D q y)
    (dgWalkingHomRefinedEvaluation A D y r) (dgWalkingHomOriginalEvaluation A D q y)
    (dgWalkingHomPrecomposeComponent A D y r)
  intro k a
  have hF := congrArg (fun f => f.f k a)
    (dgWalkingHomEvaluation_generator A D (homObject A D q y) p y
      (dgClosedPrecomposition A D r))
  have hG := congrArg (fun f => f.f k a)
    (dgWalkingHomEvaluation_generator A D (homObject A D q y) q y (𝟙 _))
  change compose A (unitElement A y).val _ _ =
    compose A _ (closedHomEquiv A D _ _ r).val _
  change ((dgWalkingHomRefinedEvaluation A D y r).map _ _).f k
    ((dgWalkingHomGenerator A (homObject A D q y)).f k a) =
      (dgClosedPrecomposition A D r).f k a at hF
  change ((dgWalkingHomOriginalEvaluation A D q y).map _ _).f k
    ((dgWalkingHomGenerator A (homObject A D q y)).f k a) = a at hG
  rw [hF, hG, unit_compose]
  exact dgClosedPrecomposition_f A D r k a

end SerrePositivity.InfinityCategories
