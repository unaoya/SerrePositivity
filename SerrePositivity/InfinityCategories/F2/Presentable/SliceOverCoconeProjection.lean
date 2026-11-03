module

public import SerrePositivity.InfinityCategories.F2.Presentable.SliceOverCoconeIso
public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationCocone

/-!
概要：二重 slice 比較は元の底の余錐への射影を厳密に保つ。
方針：二回 uncurry し、結合同型の左包含公式で同じ全射へ戻す。
規約：余錐の頂点だけでなく全余錐への射を比較する。
使われ方：底の余極限性から対象上の余極限性を回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：二重 slice 比較の射影は元の余錐の後合成そのもの。
方針：全射への uncurry の単射性で比較する。
規約：任意の形状と標的を扱う。
使われ方：対象上の余錐の底への射影による普遍性検出。 -/
lemma sliceOverCoconeForward_projection {K X : SSet.{u}}
    (x : (Δ[0] : SSet.{u}) ⟶ X) (a : K ⟶ sliceOver x) :
    sliceOverCoconeForward x a ≫
        sliceOverProjection (SSet.yonedaEquiv.symm (sliceOverAugmentationCocone x a)) =
      sliceUnderPostcomp a (sliceOverProjection x) := by
  rw [← sliceOverUncurry_projection (sliceOverCoconeForward x a)]
  apply sliceUnderUncurry_injective (a ≫ sliceOverProjection x)
  rw [sliceUnderUncurry_precomp, sliceOverCoconeForward_uncurry]
  dsimp only [sliceOverCoconeForwardDiagram]
  have hi : joinMap (𝟙 K) (joinInl (sliceUnder a) (Δ[0] : SSet.{u})) ≫
      (stableJoinAssociator K (sliceUnder a) Δ[0]).inv =
        joinInl (join K (sliceUnder a)) Δ[0] := by
    rw [← stableJoinAssociator_inl, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, hi, sliceOverUncurry_projection]
  have ht := sliceUnderUncurry_postcomp (𝟙 (sliceUnder a)) (sliceOverProjection x)
  simpa only [Category.id_comp] using ht.symm

/-- 概要：比較後の余錐の始域は元の底の余錐と一致する。
方針：全射の射影等式の零次成分を取る。
規約：元の余錐の全射を保持する。
使われ方：底の余極限余錐の始対象性を slice に移す。 -/
lemma sliceOverCoconeForward_vertex_projection {K X : SSet.{u}}
    (x : (Δ[0] : SSet.{u}) ⟶ X) (a : K ⟶ sliceOver x) (c : JoinCocone a) :
    (sliceOverProjection (SSet.yonedaEquiv.symm (sliceOverAugmentationCocone x a))).app
        (Opposite.op ⦋0⦌) ((sliceOverCoconeForward x a).app (Opposite.op ⦋0⦌) c) =
      (mapJoinCocone (sliceOverProjection x) c : JoinCocone (a ≫ sliceOverProjection x)) := by
  exact congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) c)
    (sliceOverCoconeForward_projection x a)

end SerrePositivity.InfinityCategories.F2.Presentable
