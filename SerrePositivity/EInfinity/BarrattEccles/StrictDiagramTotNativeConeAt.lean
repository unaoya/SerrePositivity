module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotUniverseNativeCone
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotUniverseIndex

/-!
概要：元の同じBK点から得たjoin錐を元のstrictなΔ図式上へ戻す。
方針：指定添字同型の逆のjoin写像で引き戻し、両境界を照合する。
規約：IS-W2 R02の一図式の錐。全図式射の族と極限性は後続の対象。
使われ方：同じ元のTot頂点の指定native錐の入口。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open scoped Simplicial
variable (A : Type u) [CommRing A]
local instance strictBETotNativeConeAtModel : ModelCategory (operad A).Algebra := modelCategory A
local instance strictBETotNativeConeAtFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩
local instance strictBETotNativeConeAtCof (Y : (operad A).Algebra) :
    IsCofibrant (framedLimitProbe A Y) := framedLimitProbe_cofibrant A Y

/-- 元の同じΔ図式について、同じ指定BK点から得たnative join錐。 -/
def strictBETotNativeConeAt (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) :
    JoinCone (strictBECosimplicialDiagram A F) := by
  refine ⟨joinMap (𝟙 (Δ[0] : SSet.{u+1}))
    (strictBETotUniverseIndexIso (AsSmall.{u} SimplexCategory)).inv ≫
      (strictBETotUniverseNativeCone A (AsSmall.{u} SimplexCategory) F).val, ?_⟩
  rw [← Category.assoc, joinInr_joinMap, Category.assoc,
    (strictBETotUniverseNativeCone A (AsSmall.{u} SimplexCategory) F).property,
    strictBETotUniverseSourceDiagram_index, Iso.inv_hom_id_assoc]

/-- 元のΔ図式へ戻しても左境界は元の同じTot頂点。 -/
theorem strictBETotNativeConeAt_vertexMap
    (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) :
    joinInl (Δ[0] : SSet.{u+1}) _ ≫ (strictBETotNativeConeAt A F).val =
      SSet.yonedaEquiv.symm ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex ((framedLimitFunctor A (AsSmall.{u} SimplexCategory)).obj F))) := by
  change joinInl _ _ ≫ (joinMap _ _ ≫ _) = _
  rw [← Category.assoc, joinInl_joinMap, Category.id_comp]
  exact strictBETotUniverseNativeCone_vertexMap A _ F

/-- 頂点の零単体も元の同じTot頂点そのもの。 -/
theorem strictBETotNativeConeAt_vertex
    (F : AsSmall.{u} SimplexCategory ⥤ (operad A).Algebra) :
    (strictBETotNativeConeAt A F).vertex = (algebraCAlgSource A).app (Opposite.op ⦋0⦌)
      (nerveVertex ((framedLimitFunctor A (AsSmall.{u} SimplexCategory)).obj F)) := by
  rw [JoinCone.vertex_eq, strictBETotNativeConeAt_vertexMap, Equiv.apply_symm_apply]

end SerrePositivity.EInfinity.BarrattEccles
