module
public import SerrePositivity.InfinityCategories.Stable.ZeroCornerSquareSpan

/-!
概要：零終点 span の可縮性と、固定した実 span 上の零隅四角形の始対象。
方針：二辺の相対持ち上げ、全制限写像、同じ厳密 fiber の比較を接続する。
規約：安定性・余極限は仮定しない。使われ方：一般安定性判定の押し出し構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
lemma zeroCornerSquareSpan_source (X : SSet.{u}) :
    zeroCornerSquareSpan X ≫ zeroOuterSpanSource X = zeroCornerSquareSource X := by
  dsimp only [zeroCornerSquareSpan, zeroOuterSpanSource, zeroOuterSpanLeftArrow,
    zeroTargetArrowSource, zeroCornerSquareSource]
  simp only [← Category.assoc, fullSubcomplexLift_ι]
  simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map,
    spanSquareBoundary_bottomEdge, stable_pre_evaluateFunctorAt]
  rfl

/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
lemma vertexFiberMap_kanEquivalenceLifting {E E' B : SSet.{u}}
    (p : E ⟶ B) (q : E' ⟶ B) (f : E ⟶ E') (hf : f ≫ q = p)
    (h : F1B.KanEquivalenceLifting f) (x : B _⦋0⦌) :
    F1B.KanEquivalenceLifting (vertexFiberMap p q f hf x) := by
  intro A D i hi he
  have := h i hi he
  exact HomotopyLimits.vertexFiberMap_hasLiftingProperty p q f hf x i

/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
def zeroCornerSquareSpanSourceFiberMap (X : SSet.{u}) (x : X _⦋0⦌) :
    vertexFiber (zeroCornerSquareSource X) x ⟶ vertexFiber (zeroOuterSpanSource X) x :=
  vertexFiberMap (zeroCornerSquareSource X) (zeroOuterSpanSource X)
    (zeroCornerSquareSpan X) (zeroCornerSquareSpan_source X) x

/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
lemma zeroCornerSquareSpanSourceFiberMap_kanEquivalenceLifting
    (X : SSet.{u}) [Quasicategory X] (x : X _⦋0⦌) :
    F1B.KanEquivalenceLifting (zeroCornerSquareSpanSourceFiberMap X x) :=
  vertexFiberMap_kanEquivalenceLifting _ _ _ _
    (zeroCornerSquareSpan_kanEquivalenceLifting X) x

/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
instance zeroCornerSquareSourceFiber_quasicategory (X : SSet.{u}) [Quasicategory X]
    (x : X _⦋0⦌) : Quasicategory (vertexFiber (zeroCornerSquareSource X) x) := by
  let q := pullback.fst (coneRestriction (horn 2 2 : SSet.{u}) X)
    (fullSubcomplexOnVertices ((ihom (horn 2 2 : SSet.{u})).obj X)
      IsZeroOuterCospanVertex).ι ≫ coneApexEvaluation (horn 2 2 : SSet.{u}) X
  let f := vertexFiberMap (zeroCornerSquareSource X) q (zeroCornerSquareConeIso X).hom
    (zeroCornerSquareConeIso_source X) x
  have : IsIso f := HomotopyLimits.vertexFiberMap_isIso _ _ _ _ _
  have : Quasicategory (vertexFiber q x) := coneInputSourceFiber_quasicategory _ x
  exact quasicategory_of_innerFibration f
end SerrePositivity.InfinityCategories
