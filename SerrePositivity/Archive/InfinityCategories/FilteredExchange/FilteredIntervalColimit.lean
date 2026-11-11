module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalDiagram
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.ComparisonWithTopologicalSpaces.FiniteInternalHomContinuity
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
概要：区間関手と filtered 余極限の交換は両端の評価を保つ。
方針：有限内部 Hom の余極限保存同型を各余錐の脚で計算する。
規約：区間関手は Fun(Δ¹,−) そのもの。
使われ方：path 置換の引き戻しの標準比較を構成する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {I : Type u} [SmallCategory I] [IsFiltered I]

/-- 概要：区間関手を取ってからの余極限と、余極限の区間関手の標準同型。
方針：Δ¹ の有限性による保存同型を逆にする。
規約：同じ宇宙の通常の filtered 図式。使われ方：path 座標の交換。 -/
def intervalColimitIso (G : I ⥤ SSet.{u}) :
    colimit (G ⋙ ihom (Δ[1] : SSet.{u})) ≅ (ihom (Δ[1] : SSet.{u})).obj (colimit G) :=
  (preservesColimitIso (ihom (Δ[1] : SSet.{u})) G).symm

/-- 概要：区間関手の余極限の比較同型は両端の評価を保つ。
方針：各余錐の脚で保存同型と評価の自然性を比較する。
規約：0 と 1 の両方を同じ式で扱う。使われ方：引き戻し比較の可換条件。 -/
lemma intervalColimitIso_endpoint (G : I ⥤ SSet.{u}) (e : Fin 2) :
    (intervalColimitIso G).hom ≫ (intervalEndpointNatTrans e).app (colimit G) =
      colim.map (diagramIntervalEndpoint G e) := by
  apply colimit.hom_ext
  intro i
  change colimit.ι (G ⋙ ihom (Δ[1] : SSet.{u})) i ≫
    (preservesColimitIso (ihom (Δ[1] : SSet.{u})) G).inv ≫
      (intervalEndpointNatTrans e).app (colimit G) = _
  rw [← Category.assoc, ι_preservesColimitIso_inv, colimit.ι_map]
  exact (intervalEndpointNatTrans e).naturality (colimit.ι G i)

end SerrePositivity.InfinityCategories.F2
