module

public import SerrePositivity.InfinityCategories.F1.RelativeHomCoslicePointedTransport
public import SerrePositivity.InfinityCategories.F1.CoherentKanLeftActionInterval

/-!
概要：実際の Hom 大域比較を、同じ反転 Hom 全体上の Kan 作用の輸送へ結ぶ。
方針：標準 coslice fiber 比較で制限し、豊穣評価の左区間自然性を使う。
規約：始点は元の相対恒等射、辺は元の豊穣評価の作用そのもの。
使われ方：大域比較の fiber 同値性を、同じ係数と恒等射の合成則から証明する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ動く始点と辺への対角輸送は、パラメーターの任意の制限と厳密に可換。 -/
lemma diagonalFiberTransport_precomp {P Q E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
    (x : P ⟶ vertexFiber p a) (c : P ⟶ intervalMappingSpace a b) (k : Q ⟶ P) :
    k ≫ diagonalFiberTransport p x c = diagonalFiberTransport p (k ≫ x) (k ≫ c) := by
  simp only [diagonalFiberTransport, ← Category.assoc, comp_lift]

/-- 元の大域比較の fiber 作用は、全反転 Hom 上で実際の豊穣 Kan 作用の輸送と同型。 -/
def relativeHomCosliceComparisonFiber_enrichedActionIso {B : SSet.{u}}
    (q r : LeftFibrationObject B) :
    FunctorIso
      (((HomotopyLimits.uliftOppositeIso (SimplicialCategory.sHom q r)).inv ≫
        HomotopyLimits.coherentCosliceFiberComparison q r) ≫
          relativeHomCosliceComparisonFiber q r)
      (diagonalFiberTransport pointedSpaceProjection (SSet.const (relativeHomPointedIdentity q))
        (SSet.opFunctor.map ((SSet.uliftFunctor.{u + 1, u}).map
          ((relativeFunctorEnrichedEvaluation q.val).map q r)) ≫
          intervalMappingCurryOfEndpoints
            (pointedReverseKanHomInterval
              ((relativeFunctorEnrichedEvaluation q.val).obj q)
              ((relativeFunctorEnrichedEvaluation q.val).obj r))
            (pointedReverseKanHomInterval_zero
              ((relativeFunctorEnrichedEvaluation q.val).obj q)
              ((relativeFunctorEnrichedEvaluation q.val).obj r))
            (pointedReverseKanHomInterval_one
              ((relativeFunctorEnrichedEvaluation q.val).obj q)
              ((relativeFunctorEnrichedEvaluation q.val).obj r)))) := by
  let k := (HomotopyLimits.uliftOppositeIso (SimplicialCategory.sHom q r)).inv ≫
    HomotopyLimits.coherentCosliceFiberComparison q r
  have e := FunctorIso.precomp (relativeHomCosliceComparisonFiber_pointedTransportIso q r) k
  rw [diagonalFiberTransport_precomp, SSet.comp_const] at e
  have hc := coherentKanLeftHomIntervalMap_naturality (relativeFunctorEnrichedEvaluation q.val) q r
  change k ≫ (cosliceFiberToIntervalMappingSpace (coherentNerveVertex q) (coherentNerveVertex r) ≫
    intervalMappingPostOfEq (leftFibrationCoherentEvaluation q.val)
      (coherentNerveVertex q) (coherentNerveVertex r)
      (relativeHomCoherentEvaluation_value q q) (relativeHomCoherentEvaluation_value q r)) = _ at hc
  rw [hc] at e
  exact e

end SerrePositivity.InfinityCategories
