module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotUniverseNativeCone
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotUniverseIndex

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元の同じBK点から得たjoin錐を元のstrictなΔ図式上へ戻す。
方針：指定添字同型の逆のjoin写像で引き戻し、両境界を照合する。
規約：IS-W2 R02の一図式の錐。全図式射の族と極限性は後続の対象。
使われ方：同じ元のTot頂点の指定native錐の入口。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]
local instance strictBETotNativeConeAtModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance strictBETotNativeConeAtFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩
local instance strictBETotNativeConeAtCof (Y : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    IsCofibrant (_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe A Y) := _root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbe_cofibrant A Y

/-- 元の同じΔ図式について、同じ指定BK点から得たnative join錐。 -/
def strictBETotNativeConeAt (F : AsSmall.{u} SimplexCategory ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    JoinCone (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBECosimplicialDiagram A F) := by
  refine ⟨joinMap (𝟙 (Δ[0] : SSet.{u+1}))
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniverseIndexIso (AsSmall.{u} SimplexCategory)).inv ≫
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniverseNativeCone A (AsSmall.{u} SimplexCategory) F).val, ?_⟩
  rw [← Category.assoc, joinInr_joinMap, Category.assoc,
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniverseNativeCone A (AsSmall.{u} SimplexCategory) F).property,
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniverseSourceDiagram_index, Iso.inv_hom_id_assoc]

/-- 元のΔ図式へ戻しても左境界は元の同じTot頂点。 -/
theorem strictBETotNativeConeAt_vertexMap
    (F : AsSmall.{u} SimplexCategory ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    joinInl (Δ[0] : SSet.{u+1}) _ ≫ (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotNativeConeAt A F).val =
      SSet.yonedaEquiv.symm ((_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A (AsSmall.{u} SimplexCategory)).obj F))) := by
  change joinInl _ _ ≫ (joinMap _ _ ≫ _) = _
  rw [← Category.assoc, joinInl_joinMap, Category.id_comp]
  exact _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotUniverseNativeCone_vertexMap A _ F

/-- 頂点の零単体も元の同じTot頂点そのもの。 -/
theorem strictBETotNativeConeAt_vertex
    (F : AsSmall.{u} SimplexCategory ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotNativeConeAt A F).vertex = (_root_.SerrePositivity.EInfinity.BarrattEccles.algebraCAlgSource A).app (Opposite.op ⦋0⦌)
      (nerveVertex ((_root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitFunctor A (AsSmall.{u} SimplexCategory)).obj F)) := by
  rw [JoinCone.vertex_eq, _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotNativeConeAt_vertexMap, Equiv.apply_symm_apply]

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
