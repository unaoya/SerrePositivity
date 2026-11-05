module
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakSpanZeroSimplexFiber
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakSpanKanQuotientUnitRecovery
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakSpanKanQuotientFixedFiber

/-!
概要：同じ商上の実単位の零単体制限を、文字通り元の終点の fiber へ戻す。
方針：元の終点の等式による座標輸送と元の fiber 包含の厳密照合を使う。
規約：同じ実全族単位・指定商比較・元の終点を保持する。
使われ方：K-B-S の実全族写像の全 fiber の Kan 単位回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x y : B.obj _⦋0⦌)

/-- 概要：元の固定終点の零単体上で、同じ実単位の商像を元の商 fiber へ送る。
方針：元の固定 span と商 fiber の終点だけを厳密な等式で輸送する。
規約：元の実単位の制限を使い、別の単位を選ばない。
使われ方：同じ元の全族写像の全 fiber と比較する零単体制限。 -/
def weakSpanKanQuotientZeroUnit :
    fixedMarkedSpans B.obj (weakEquivalences i) x y ⟶
      vertexFiber (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x))
        (q.hom.app (Opposite.op ⦋0⦌) y) :=
  eqToHom (congrArg (fun z => fixedMarkedSpans B.obj (weakEquivalences i) x z)
    (transportSimplexFirstVertexMap_zeroIndex y).symm) ≫
    weakSpanKanQuotientSimplexUnitFiber h x (transportSimplexIndex (n := ⦋0⦌) y) ≫
    eqToHom (congrArg (vertexFiber
      (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x)))
      (congrArg (q.hom.app (Opposite.op ⦋0⦌)) (transportSimplexFirstVertexMap_zeroIndex y)))

/-- 概要：同じ零単体の実単位は、元の全族比較からの零単体 fiber 制限そのもの。
方針：同じ実 fiber の包含後で等式輸送・両実 fiber 写像の包含式を計算する。
規約：同じ元の全族射への後合成を全単体で厳密に回収する。
使われ方：元の全族の全固定 fiber 比較を Kan 単位回収へ接続する。 -/
theorem weakSpanKanQuotientZeroUnit_eq_fixedFiber :
    weakSpanKanQuotientZeroUnit h x y = weakSpanKanQuotientZeroSimplexFixedFiber h x y := by
  apply vertexFiber_hom_ext
  simp only [weakSpanKanQuotientZeroUnit, Category.assoc, vertexFiberTransport_ι,
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientSimplexUnitFiber]
  erw [vertexFiberTransport_ι
    (smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram h x))
    (congrArg (q.hom.app (Opposite.op ⦋0⦌)) (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.transportSimplexFirstVertexMap_zeroIndex y))]
  erw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientSimplexFiberMap_ι h x (transportSimplexIndex (n := ⦋0⦌) y)]
  rw [← Category.assoc _ (vertexFiberι
    (smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanCoherentDiagram i x))
      (nerveVertex (transportSimplexIndex (n := ⦋0⦌) y)))
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientSimplexUnstraighteningMap h x), vertexFiberMap_ι]
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientZeroSimplexFixedFiber, vertexFiberLift_ι]
  change _ = weakSpanFixedZeroSimplexLift i x y ≫
    weakSpanKanUnstraighteningUnit i x ≫ weakSpanKanQuotientSimplexUnstraighteningMap h x
  have hs := weakSpanZeroSimplexFiberIso_inclusion i x y
  dsimp only [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanZeroSimplexFiberIso, Iso.trans_hom, eqToIso.hom] at hs
  simpa only [Category.assoc] using! congrArg (fun f => f ≫
    weakSpanKanUnstraighteningUnit i x ≫ weakSpanKanQuotientSimplexUnstraighteningMap h x) hs

end SerrePositivity.KST.Fibration
