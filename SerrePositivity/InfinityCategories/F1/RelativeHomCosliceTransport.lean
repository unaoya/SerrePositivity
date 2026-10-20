module

public import SerrePositivity.InfinityCategories.F1.RelativeHomCosliceComparison
public import SerrePositivity.InfinityCategories.F1.CosliceUniversalPrismTransport

/-!
概要：Hom 関手への実際の大域比較の fiber 作用を、恒等点からの標準輸送と比較する。
方針：同じ大域射の恒等錐での値を使い、普遍 coslice prism の一意性を適用する。
規約：始点・射影・元の fiber 比較を保ち、各 fiber の逆同値を別に選ばない。
使われ方：この同じ比較の同値性を、Hom の Kan 作用の恒等則へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 恒等点は、unstraightening の元の射影で指定した対象の頂点へ厳密に写る。 -/
lemma relativeHomUnstraighteningIdentity_projection {B : SSet.{u}}
    (q : LeftFibrationObject B) :
    (leftUnstraighteningProjection (leftFibrationCoherentEvaluation q.val)).app
      (Opposite.op ⦋0⦌) (relativeHomUnstraighteningIdentity q).val = coherentNerveVertex q := by
  simpa only [PinchedHom.constant_zero] using (relativeHomUnstraighteningIdentity q).property

/-- 元の大域比較の native な fiber 作用は、同じ恒等点からの標準 coslice 輸送。 -/
def relativeHomCosliceComparison_nativeTransportIso {B : SSet.{u}}
    (q r : LeftFibrationObject B) :
    FunctorIso
      (vertexFiberMap _ _ (relativeHomCosliceComparison q)
        (relativeHomCosliceComparison_projection q) (coherentNerveVertex r))
      (diagonalFiberTransport
        (leftUnstraighteningProjection (leftFibrationCoherentEvaluation q.val))
        (SSet.const (relativeHomUnstraighteningIdentity q))
        (cosliceFiberToIntervalMappingSpace (coherentNerveVertex q) (coherentNerveVertex r))) :=
  leftFibrationCosliceMap_transportIso
    (leftUnstraighteningProjection (leftFibrationCoherentEvaluation q.val))
    (coherentNerveVertex q) (relativeHomUnstraighteningIdentity q).val
    (relativeHomUnstraighteningIdentity_projection q) (relativeHomCosliceComparison q)
    (relativeHomCosliceComparison_projection q) (relativeHomCosliceComparison_identity q)
    (coherentNerveVertex r)

/-- 実際の pointed fiber 比較は、この同じ native 輸送を既存の fiber 同型で移したもの。 -/
def relativeHomCosliceComparisonFiber_nativeTransportIso {B : SSet.{u}}
    (q r : LeftFibrationObject B) :
    FunctorIso (relativeHomCosliceComparisonFiber q r)
      (diagonalFiberTransport
        (leftUnstraighteningProjection (leftFibrationCoherentEvaluation q.val))
        (SSet.const (relativeHomUnstraighteningIdentity q))
        (cosliceFiberToIntervalMappingSpace (coherentNerveVertex q) (coherentNerveVertex r)) ≫
          (relativeHomUnstraighteningFiberIso q r).hom) :=
  FunctorIso.postcomp (relativeHomCosliceComparison_nativeTransportIso q r)
    (relativeHomUnstraighteningFiberIso q r).hom

end SerrePositivity.InfinityCategories
