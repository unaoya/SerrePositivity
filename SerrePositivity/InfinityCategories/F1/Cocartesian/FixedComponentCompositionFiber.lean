module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.FirstTriangleFamily
public import SerrePositivity.InfinityCategories.F1.Cocartesian.IntervalCompositionFiber

/-!
概要：元の固定成分比較を、指定第一三角形の fiber と同じ外ホーン fiber へ制限する。
方針：第一三角形の定値性で fiber に持ち上げ、検証済みの同じ pullback の同型を使う。
規約：元の比較射と第二三角形への作用を厳密に保持する。
使われ方：元の後合成 fiber と指定外ホーン fiber の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable (F G : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2)))
variable (b : ((SSet.uliftFunctor.{u + 1, u}).obj
  (SimplicialCategory.sHom (cocartesianTransportDiagramValue F (ULift.up 1))
    (cocartesianTransportDiagramValue G (ULift.up 1)))) _⦋0⦌)
local notation "v" => NatTrans.app
  (coherentHomIntervalComparison (cocartesianTransportDiagramValue F (ULift.up 1))
    (cocartesianTransportDiagramValue G (ULift.up 1))) (Opposite.op ⦋0⦌) b
local notation "S" => vertexFiber (cocartesianHomSourceComponent F G (ULift.up 1)) b
local notation "p" => cocartesianIntervalCompositionTriangleMap F G v
local notation "s₀" => cocartesianIntervalSourceCompositionVertex F G b
local notation "q" => cocartesianIntervalOuterHornMap F G v
local notation "r" => NatTrans.app (pre (SSet.Subcomplex.ι (horn 2 2))) CatInfinity

/-- 元の比較の第一三角形への制限は、同じ指定合成頂点に厳密に定値。 -/
lemma cocartesianHomFixedComponentComparison_compositionTriangle :
    cocartesianHomFixedComponentComparison F G (ULift.up 1) b ≫ p = SSet.const s₀ := by
  apply innerTriangleExtensionUncurry_injective
    (composableEdgeHorn (cocartesianIntervalCompositionFirstEdge F)
      (intervalMappingEdgeOfVertex v))
  rw [cocartesianIntervalCompositionTriangleMap_uncurry,
    cocartesianHomFixedComponentComparison_firstTriangle,
    cocartesianIntervalSourceCompositionVertex_uncurry]

/-- 元の比較を、同じ指定第一三角形の fiber へ制限する。 -/
def cocartesianHomFixedComponentCompositionFiberComparison : S ⟶ vertexFiber p s₀ :=
  vertexFiberLift p s₀ (cocartesianHomFixedComponentComparison F G (ULift.up 1) b)
    (cocartesianHomFixedComponentComparison_compositionTriangle F G b)

/-- 指定第一三角形の fiber への制限は、元の比較射そのものを回収する。 -/
lemma cocartesianHomFixedComponentCompositionFiberComparison_ι :
    cocartesianHomFixedComponentCompositionFiberComparison F G b ≫ vertexFiberι p s₀ =
      cocartesianHomFixedComponentComparison F G (ULift.up 1) b :=
  vertexFiberLift_ι _ _ _ _

/-- 元の比較を、同じ指定された外ホーンの延長 fiber へ移す。 -/
def cocartesianHomFixedComponentOuterHornComparison :
    S ⟶ vertexFiber r (NatTrans.app q (Opposite.op ⦋0⦌) s₀) :=
  cocartesianHomFixedComponentCompositionFiberComparison F G b ≫
    (cocartesianIntervalOuterHornFiberIso F G v s₀).hom

/-- 外ホーン fiber からの既存の同値へ続けると、元の比較射を厳密に回収する。 -/
lemma cocartesianHomFixedComponentOuterHornComparison_realize :
    cocartesianHomFixedComponentOuterHornComparison F G b ≫
        cocartesianIntervalOuterHornFiberComparison F G v s₀ =
      cocartesianHomFixedComponentComparison F G (ULift.up 1) b := by
  unfold cocartesianHomFixedComponentOuterHornComparison
    cocartesianIntervalOuterHornFiberComparison
  rw [Category.assoc, ← Category.assoc
    (cocartesianIntervalOuterHornFiberIso F G v s₀).hom
    (cocartesianIntervalOuterHornFiberIso F G v s₀).inv,
    Iso.hom_inv_id, Category.id_comp,
    cocartesianHomFixedComponentCompositionFiberComparison_ι]

/-- 同じ外ホーン比較の第二三角形は、元の比較の第二三角形そのもの。 -/
lemma cocartesianHomFixedComponentOuterHornComparison_second :
    cocartesianHomFixedComponentOuterHornComparison F G b ≫
        vertexFiberι r (NatTrans.app q (Opposite.op ⦋0⦌) s₀) =
      cocartesianHomFixedComponentComparison F G (ULift.up 1) b ≫
        cocartesianIntervalSecondTriangleMap F G v := by
  unfold cocartesianHomFixedComponentOuterHornComparison
  rw [Category.assoc, cocartesianIntervalOuterHornFiberIso_hom_ι, ← Category.assoc,
    cocartesianHomFixedComponentCompositionFiberComparison_ι]

end SerrePositivity.InfinityCategories
