module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.NativeMappingVertexEdge
public import SerrePositivity.InfinityCategories.Derived.SuspensionAction.NativeTarget
public import SerrePositivity.InfinityCategories.Derived.DGSuspensionCoherentActionInput

/-!
概要：切替後の正本懸垂の native 商作用を、実入力射の端点固定辺と比較する。
方針：D-S の厳密な頂点回収を、同じ native 頂点の標準辺へ写す。
規約：最終 map の辺との比較は別入力。両端の dg 入力は等号で固定する。
使われ方：D-S 工程4 edgeIso の準備と、最終作用への比較の接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded KST.SConstruction KST.NonConnective
open scoped Simplicial
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) [Fact κ.IsRegular]
  (hκ : Cardinal.aleph0 < κ)
variable {A B : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B)

/-- D-S の native 商作用の f での値を、同じ固定懸垂を端点とする辺に読む。 -/
def dgSuspensionQuotientNativeEdge :
    SSet.Edge (coherentNerveVertex (dgKappaSuspensionKInput R A
        (dgKappaUnconditionalStageProvider.{u, v} R κ hκ A).cone))
      (coherentNerveVertex (dgKappaSuspensionKInput R B
        (dgKappaUnconditionalStageProvider.{u, v} R κ hκ B).cone)) :=
  dgNativeMappingVertexEdge R _ _
    ((dgSuspensionQuotientNativeMap R κ hκ A B).app (Opposite.op ⦋0⦌)
      (dgSuspensionResolvedEpsilonVertex R κ hκ A B f))

/-- native 商作用から読む辺は、同じ正本 data の厳密入力射の標準辺そのもの。 -/
lemma dgSuspensionQuotientNativeEdge_eq :
    dgSuspensionQuotientNativeEdge R κ hκ f =
      coherentNerveEdge (dgKappaSuspensionInputMap R A B
          (dgKappaUnconditionalStageProvider.{u, v} R κ hκ A).cone
          (dgKappaUnconditionalStageProvider.{u, v} R κ hκ B).cone
        (dgSuspensionUnconditionalMapData R κ hκ f)) := by
  unfold dgSuspensionQuotientNativeEdge
  rw [dgSuspensionQuotientNativeMap_vertex, dgNativeMappingVertexEdge_vertex]
  rfl

/-- 端点を動かさない、正本実入力辺への指定同型。 -/
def dgSuspensionQuotientNativeEdgeIso :
    VertexIso (intervalMappingVertexOfEdge (dgSuspensionQuotientNativeEdge R κ hκ f))
      (intervalMappingVertexOfEdge (coherentNerveEdge
        (dgKappaSuspensionInputMap R A B
          (dgKappaUnconditionalStageProvider.{u, v} R κ hκ A).cone
          (dgKappaUnconditionalStageProvider.{u, v} R κ hκ B).cone
          (dgSuspensionUnconditionalMapData R κ hκ f)))) := by
  rw [dgSuspensionQuotientNativeEdge_eq]

end SerrePositivity.InfinityCategories
