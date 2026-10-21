module

public import SerrePositivity.InfinityCategories.F1.CocartesianPostcompositionFiber
public import SerrePositivity.InfinityCategories.F1.CocartesianFixedComponentCompositionFiber

/-!
概要：元の後合成 fiber から、同じ指定外ホーン fiber への実際の比較射を定める。
方針：元の source の固定成分との厳密な同型で、構成済みの同じ外ホーン比較を移す。
規約：元の比較と第二三角形を厳密に回収する。
使われ方：後合成の標準 Hom 比較を用いた、残る局所同値性の証明。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable (F G : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2)))
variable (b : ((SSet.uliftFunctor.{u + 1, u}).obj
  (SimplicialCategory.sHom (cocartesianTransportDiagramValue F (ULift.up 1))
    (cocartesianTransportDiagramValue G (ULift.up 1)))) _⦋0⦌)
local notation "v" => NatTrans.app
  (coherentHomIntervalComparison (cocartesianTransportDiagramValue F (ULift.up 1))
    (cocartesianTransportDiagramValue G (ULift.up 1))) (Opposite.op ⦋0⦌) b
local notation "s₀" => cocartesianIntervalSourceCompositionVertex F G b
local notation "q" => cocartesianIntervalOuterHornMap F G v
local notation "r" => NatTrans.app (pre (SSet.Subcomplex.ι (horn 2 2))) CatInfinity

/-- 元の後合成 fiber から同じ指定外ホーン fiber への、元の作用を保つ比較。 -/
def cocartesianPostcompositionOuterHornComparison :
    (SSet.uliftFunctor.{u + 1, u}).obj (cocartesianIntervalPostcompositionFiber F G b) ⟶
      vertexFiber r (NatTrans.app q (Opposite.op ⦋0⦌) s₀) :=
  (cocartesianHomSourcePostcompositionFiberIso F G b).inv ≫
    cocartesianHomFixedComponentOuterHornComparison F G b

/-- 元の source fiber の同型に沿って戻すと、同じ元の外ホーン比較になる。 -/
lemma cocartesianPostcompositionOuterHornComparison_source :
    (cocartesianHomSourcePostcompositionFiberIso F G b).hom ≫
        cocartesianPostcompositionOuterHornComparison F G b =
      cocartesianHomFixedComponentOuterHornComparison F G b := by
  rw [cocartesianPostcompositionOuterHornComparison, ← Category.assoc,
    Iso.hom_inv_id, Category.id_comp]

/-- 元の後合成 fiber からの比較も、既存の同値に続けると元の比較射を回収する。 -/
lemma cocartesianPostcompositionOuterHornComparison_realize :
    cocartesianPostcompositionOuterHornComparison F G b ≫
        cocartesianIntervalOuterHornFiberComparison F G v s₀ =
      (cocartesianHomSourcePostcompositionFiberIso F G b).inv ≫
        cocartesianHomFixedComponentComparison F G (ULift.up 1) b := by
  rw [cocartesianPostcompositionOuterHornComparison, Category.assoc,
    cocartesianHomFixedComponentOuterHornComparison_realize]

/-- 同じ後合成 fiber の比較の第二三角形も、元の比較の第二三角形そのもの。 -/
lemma cocartesianPostcompositionOuterHornComparison_second :
    cocartesianPostcompositionOuterHornComparison F G b ≫
        vertexFiberι r (NatTrans.app q (Opposite.op ⦋0⦌) s₀) =
      (cocartesianHomSourcePostcompositionFiberIso F G b).inv ≫
        cocartesianHomFixedComponentComparison F G (ULift.up 1) b ≫
          cocartesianIntervalSecondTriangleMap F G v := by
  rw [cocartesianPostcompositionOuterHornComparison, Category.assoc,
    cocartesianHomFixedComponentOuterHornComparison_second]

end SerrePositivity.InfinityCategories
