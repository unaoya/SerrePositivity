module

public import SerrePositivity.InfinityCategories.F1.IntervalMappingPostcompositionVertices

/-!
概要：端点を正規化した区間写像空間の後合成と、標的の同型による同型。
方針：展開した区間族への後合成で両方向の逆写像則を確認する。
規約：値域に充填性を課さない。
使われ方：底の同型による普遍輸送のパラメーター比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：端点を正規化した後合成の展開は元の区間族の後合成。
方針：curry の逆関係とパラメーターの自然性を使う。
規約：任意のパラメーターからの族を扱う。
使われ方：同型の逆射による端点の表示変更。 -/
lemma intervalMappingPostOfEq_uncurry {T X Y : SSet.{u}} (f : X ⟶ Y)
    (x y : X _⦋0⦌) {x' y' : Y _⦋0⦌} (hx : f.app _ x = x') (hy : f.app _ y = y')
    (g : T ⟶ intervalMappingSpace x y) :
    intervalMappingUncurry (g ≫ intervalMappingPostOfEq f x y hx hy) =
      intervalMappingUncurry g ≫ f := by
  rw [intervalMappingUncurry_precomp, intervalMappingPostOfEq,
    intervalMappingUncurry_curryOfEndpoints, ← Category.assoc,
    ← intervalMappingUncurry_precomp, Category.comp_id]

/-- 概要：単体集合の同型は対応する端点の区間写像空間の同型を与える。
方針：同型の逆の端点を正規化し、展開した区間族で逆写像則を確認する。
規約：順射は既存の intervalMappingPost のまま。
使われ方：底の同型に沿う普遍輸送の同値性の移送。 -/
def intervalMappingPostIso {X Y : SSet.{u}} (e : X ≅ Y) (x y : X _⦋0⦌) :
    intervalMappingSpace x y ≅ intervalMappingSpace (e.hom.app _ x) (e.hom.app _ y) := by
  have hx : e.inv.app _ (e.hom.app _ x) = x :=
    ConcreteCategory.congr_hom (NatTrans.congr_app e.hom_inv_id _) x
  have hy : e.inv.app _ (e.hom.app _ y) = y :=
    ConcreteCategory.congr_hom (NatTrans.congr_app e.hom_inv_id _) y
  refine ⟨intervalMappingPost e.hom x y,
    intervalMappingPostOfEq e.inv (e.hom.app _ x) (e.hom.app _ y) hx hy, ?_, ?_⟩
  · apply intervalMappingUncurry_injective x y
    rw [intervalMappingPostOfEq_uncurry, intervalMappingPost_universal_uncurry,
      Category.assoc, e.hom_inv_id, Category.comp_id]
  · apply intervalMappingUncurry_injective _ _
    rw [intervalMappingPost_uncurry]
    have h := intervalMappingPostOfEq_uncurry e.inv (e.hom.app _ x) (e.hom.app _ y) hx hy
      (𝟙 (intervalMappingSpace (e.hom.app _ x) (e.hom.app _ y)))
    rw [Category.id_comp] at h
    rw [h, Category.assoc, e.inv_hom_id, Category.comp_id]

end SerrePositivity.InfinityCategories
