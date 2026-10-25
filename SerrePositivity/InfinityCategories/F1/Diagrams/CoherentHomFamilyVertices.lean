module

public import SerrePositivity.InfinityCategories.F1.Diagrams.TetrahedronFamilyVertices
public import SerrePositivity.InfinityCategories.F1.Coherent.HomIntervalVertices

/-!
概要：元の豊穣 Hom 全族の標準区間像を、各入力の元の射と照合する。
方針：uncurry の同じ入力頂点での評価と、標準 Hom 比較の零単体を計算する。
規約：全族を点ごとの射へ置き換えず、ここではその制限式だけを公開する。
使われ方：Ind-S (9) の制御二単体の短辺と固定全ホーン族の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 区間写像空間の全族を入力頂点で制限した射は、同じ関手頂点を表す。 -/
lemma intervalMappingUncurry_familyAtVertex {K X : SSet.{u}} {x y : X _⦋0⦌}
    (r : K ⟶ intervalMappingSpace x y) (k : K _⦋0⦌) :
    functorVertex (familyAtVertex (intervalMappingUncurry r) k) =
      (r.app (Opposite.op ⦋0⦌) k).val := by
  rw [← curry_app_vertex]
  change (curry (uncurry (r ≫ vertexFiberι _ _))).app (Opposite.op ⦋0⦌) k = _
  rw [curry_uncurry]
  rfl

/-- 標準 coherent 区間像の同じ入力での辺は、元の豊穣射の辺そのもの。 -/
lemma coherentHomIntervalFamily_vertex
    {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y : C}
    {K : SSet.{max u v}}
    (f : K ⟶ (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y))
    (k : K _⦋0⦌) :
    familyAtVertex ((Δ[1] ◁ f) ≫ intervalMappingUncurry (coherentHomIntervalComparison X Y)) k =
      SSet.yonedaEquiv.symm (coherentNerveEdge
        ((SimplicialCategory.homEquiv' X Y).symm (f.app (Opposite.op ⦋0⦌) k).down)).edge := by
  rw [← intervalMappingUncurry_precomp]
  apply functorVertex_injective
  rw [intervalMappingUncurry_familyAtVertex]
  change ((coherentHomIntervalComparison X Y).app (Opposite.op ⦋0⦌)
    (ULift.up (f.app (Opposite.op ⦋0⦌) k).down)).val = _
  rw [coherentHomIntervalComparison_vertex]
  rfl

end SerrePositivity.InfinityCategories
