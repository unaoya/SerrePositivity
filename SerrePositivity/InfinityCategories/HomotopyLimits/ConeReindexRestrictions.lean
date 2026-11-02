module

public import SerrePositivity.InfinityCategories.Core.ReindexSliceOver
public import SerrePositivity.InfinityCategories.F2.CatInfinity.NativeConeLeg

/-!
概要：形状同型による native 錐の再添字が、元の頂点と脚の全一単体を保持する。
方針：元の joinMap と標準脚の包含の可換性を厳密に計算する。
規約：充填性・有限性は不要。元の全錐の射を保持する。
使われ方：有限 coherent 積の一般添字への再添字と全脚の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の再添字錐の全射は、元の形状の join 同型の前合成そのもの。 -/
lemma joinCone_reindexIso_val {K L X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (e : L ≅ K) :
    (c.reindexIso e).val = joinMap (𝟙 _) e.hom ≫ c.val := rfl

/-- 元の形状同型による再添字は、元の錐の頂点を厳密に保持する。 -/
lemma joinCone_reindexIso_vertex {K L X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (e : L ≅ K) : (c.reindexIso e).vertex = c.vertex := by
  change SSet.yonedaEquiv (joinInl _ _ ≫ (c.reindexIso e).val) = _
  rw [joinCone_reindexIso_val, ← Category.assoc, joinInl_joinMap, Category.id_comp]
  rfl

/-- 元の脚の包含は、形状の写像と全一単体で可換。 -/
lemma coneLegInclusion_naturality {K L : SSet.{u}} (a : L ⟶ K) (k : L _⦋0⦌) :
    F2.coneLegInclusion k ≫ joinMap (𝟙 _) a =
      F2.coneLegInclusion (a.app (Opposite.op ⦋0⦌) k) := by
  rw [F2.coneLegInclusion, Category.assoc, ← joinMap_comp, Category.id_comp,
    F2.coneLegInclusion, SSet.yonedaEquiv_symm_comp]

/-- 元の再添字錐の各脚は、元の像の頂点での脚と同じ全一単体。 -/
lemma nativeConeLeg_reindexIso_edge {K L X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (e : L ≅ K) (k : L _⦋0⦌) :
    (F2.nativeConeLeg (c.reindexIso e) k).edge =
      (F2.nativeConeLeg c (e.hom.app (Opposite.op ⦋0⦌) k)).edge := by
  change SSet.yonedaEquiv (F2.coneLegInclusion k ≫ (c.reindexIso e).val) =
    SSet.yonedaEquiv (F2.coneLegInclusion _ ≫ c.val)
  rw [joinCone_reindexIso_val, ← Category.assoc, coneLegInclusion_naturality]

end SerrePositivity.InfinityCategories.HomotopyLimits
