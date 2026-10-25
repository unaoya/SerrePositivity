module

public import SerrePositivity.InfinityCategories.F2.Presentable.CoconeSliceImageMap

/-!
概要：余錐の頂点で正規化した像を、元の任意の等しい点射上の slice へ全関手として戻す。
方針：両固定点の厳密同型と全 uncurry の単射性を使う。
規約：元の後合成と全図式の可換式を保持する。
使われ方：μ-small 全余錐の像を元の fiber の底上へ揃える。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：固定点移送は正規化した像と元の slice 後合成を全射として可換にする。
方針：全 uncurry で固定点の等号移送を除く。
規約：全関手の厳密な等式。
使われ方：元の fiber の全余錐比較。 -/
lemma coconeSliceImageMap_transport {K E B : SSet.{u}} {D : K ⟶ E}
    (c : JoinCocone D) (p : E ⟶ B) (a : (Δ[0] : SSet.{u}) ⟶ E)
    (ha : SSet.yonedaEquiv.symm c.vertex = a) :
    coconeSliceImageMap c p ≫
      eqToHom (congrArg sliceOver
        ((coconeSliceImagePoint_eq c p).symm.trans (congrArg (fun f ↦ f ≫ p) ha))) =
    eqToHom (congrArg sliceOver ha) ≫ sliceOverPostcomp a p := by
  apply sliceOverUncurry_injective (a ≫ p)
  rw [sliceOverUncurry_eqToHom
    ((coconeSliceImagePoint_eq c p).symm.trans (congrArg (fun f ↦ f ≫ p) ha)),
    sliceOverUncurry_postcomp]
  have h := sliceOverUncurry_eqToHom ha (𝟙 (sliceOver (SSet.yonedaEquiv.symm c.vertex)))
  simp only [Category.id_comp] at h
  rw [h]
  simpa only [Category.id_comp] using coconeSliceImageMap_uncurry c p
    (𝟙 (sliceOver (SSet.yonedaEquiv.symm c.vertex)))

end SerrePositivity.InfinityCategories.F2.Presentable
