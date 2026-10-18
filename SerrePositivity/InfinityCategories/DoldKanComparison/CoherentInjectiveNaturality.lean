module

public import SerrePositivity.InfinityCategories.DoldKanComparison.CoherentVertexImage

/-!
# 比較単体の有限頂点集合上で単射な引き戻し

概要：順序写像が選んだ頂点集合上で単射なら、比較単体のその成分は dg 引き戻しと一致する。
方針：持ち上げた内部座標の像と降順の立方体評価の自然性を使う。
規約：順序写像全体の単射性は要求しない。非単射の成分は別途扱う。
使われ方：HA 1.3.1.16、Kerodon 2.5.9 の比較写像の自然性の単射分岐。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DoldKanComparison
open CategoryTheory DifferentialGraded
open scoped Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：有限頂点集合上で単射な引き戻しでは比較成分族と dg 引き戻しが一致する。
方針：両側の hom を内部点の立方体評価にし、内部座標の像の同定を通じて比較する。
規約：端点・次数の証明は既存の dg nerve の引き戻しと同じものを使う。
使われ方：Kerodon 2.5.9 の全単調写像での自然性の単射の場合。 -/
lemma coherentSimplexData_pullback_hom_of_inj {m n : ℕ}
    (s : (doldKanCoherentNerve (R := R) (D := D)) _⦋n⦌)
    (α : Fin (m + 1) →o Fin (n + 1)) (I : Finset (Fin (m + 1)))
    (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (DGNerve.Index.nonempty hI))
    (hb : b = I.max' (DGNerve.Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ))
    (hi : Set.InjOn α (I : Set _)) :
    (coherentSimplexData ((SimplicialThickening.functor α.uliftMap).comp SSet s)).hom
      I a b k hI ha hb hk =
        ((coherentSimplexData s).pullback α).hom I a b k hI ha hb hk := by
  rw [DGNerve.SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi]
  have ha₀ : IsLeast (I : Set _) a := by rw [ha]; exact I.isLeast_min' _
  have hb₀ : IsGreatest (I : Set _) b := by rw [hb]; exact I.isGreatest_max' _
  have hab : a < b := by rw [ha, hb]; exact I.min'_lt_max'_of_card (by omega)
  have hα : StrictMonoOn α (I : Set _) :=
    (α.monotone.monotoneOn _).strictMonoOn_of_injOn hi
  have hfab : α a < α b := hα ha₀.1 hb₀.1 hab
  have hiU := coherentVertexSet_injOn.{u} α I hi
  have haU := coherentVertexSet_isLeast.{u} ha₀
  have hbU := coherentVertexSet_isGreatest.{u} hb₀
  let hS := coherentInterior_image_bounds α.uliftMap (coherentVertexSet.{u} I) haU hbU hiU
  have hcoord : pathCubeImageSet α.uliftMap (coherentVertexInterior.{u} I a b) hS =
      coherentVertexInterior (I.image α) (α a) (α b) := by
    change pathCubeImageSet _ (coherentInteriorSet _ _ _) _ = coherentInteriorSet _ _ _
    rw [coherentInteriorSet_image α.uliftMap (coherentVertexSet I) haU hbU hiU]
    congr 1
    ext z
    simp only [coherentVertexSet, Finset.mem_image]
    constructor
    · rintro ⟨x, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨α t, ⟨t, ht, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨ULift.up t, ⟨t, ht, rfl⟩, rfl⟩
  apply eq_of_heq
  apply (coherentSimplexData_hom_heq _ I a b k hI ha hb hk).trans
  apply (coherentCubeComponent_image_heq s α.uliftMap
    (show (ULift.up a : ULift.{u} (Fin (m + 1))) < ULift.up b from hab)
    (show (ULift.up (α a) : ULift.{u} (Fin (n + 1))) < ULift.up (α b) from hfab)
    (coherentVertexInterior I a b) hS
    (coherentInterior_image_strictMono α.uliftMap (coherentVertexSet I) hiU)).trans
  apply (coherentCubeComponent_heq_of_set_eq s _ _ _ hcoord).trans
  exact (coherentSimplexData_hom_heq _ _ _ _ _ _ _ _ _).symm

end SerrePositivity.InfinityCategories.DoldKanComparison
