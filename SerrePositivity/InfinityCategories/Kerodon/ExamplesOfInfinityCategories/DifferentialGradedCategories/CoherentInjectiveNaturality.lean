module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentVertexImage

/-!
# 比較単体の有限頂点集合上で単射な引き戻し

概要：順序写像が選んだ頂点集合上で単射なら、比較単体のその成分は dg 引き戻しと一致する。
方針：持ち上げた内部座標の像と降順の立方体評価の自然性を使う。
規約：順序写像全体の単射性は要求しない。非単射の成分は別途扱う。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の比較写像の自然性の単射分岐。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：有限頂点集合上で単射な引き戻しでは比較成分族と dg 引き戻しが一致する。
方針：両側の hom を内部点の立方体評価にし、内部座標の像の同定を通じて比較する。
規約：端点・次数の証明は既存の dg nerve の引き戻しと同じものを使う。
使われ方：Kerodon 2.5.9（Tag 00SC） の全単調写像での自然性の単射の場合。 -/
lemma coherentSimplexData_pullback_hom_of_inj {m n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := R) (D := D)) _⦋n⦌)
    (α : Fin (m + 1) →o Fin (n + 1)) (I : Finset (Fin (m + 1)))
    (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ))
    (hi : Set.InjOn α (I : Set _)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplexData ((SimplicialThickening.functor α.uliftMap).comp SSet s)).hom
      I a b k hI ha hb hk =
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplexData s).pullback α).hom I a b k hI ha hb hk := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi]
  have ha₀ : IsLeast (I : Set _) a := by rw [ha]; exact I.isLeast_min' _
  have hb₀ : IsGreatest (I : Set _) b := by rw [hb]; exact I.isGreatest_max' _
  have hab : a < b := by rw [ha, hb]; exact I.min'_lt_max'_of_card (by omega)
  have hα : StrictMonoOn α (I : Set _) :=
    (α.monotone.monotoneOn _).strictMonoOn_of_injOn hi
  have hfab : α a < α b := hα ha₀.1 hb₀.1 hab
  have hiU := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexSet_injOn.{u} α I hi
  have haU := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexSet_isLeast.{u} ha₀
  have hbU := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexSet_isGreatest.{u} hb₀
  let hS := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentInterior_image_bounds α.uliftMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexSet.{u} I) haU hbU hiU
  have hcoord : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeImageSet α.uliftMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexInterior.{u} I a b) hS =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexInterior (I.image α) (α a) (α b) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeImageSet _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentInteriorSet _ _ _) _ = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentInteriorSet _ _ _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentInteriorSet_image α.uliftMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexSet I) haU hbU hiU]
    congr 1
    ext z
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexSet, Finset.mem_image]
    constructor
    · rintro ⟨x, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨α t, ⟨t, ht, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨ULift.up t, ⟨t, ht, rfl⟩, rfl⟩
  apply eq_of_heq
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplexData_hom_heq _ I a b k hI ha hb hk).trans
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponent_image_heq s α.uliftMap
    (show (ULift.up a : ULift.{u} (Fin (m + 1))) < ULift.up b from hab)
    (show (ULift.up (α a) : ULift.{u} (Fin (n + 1))) < ULift.up (α b) from hfab)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexInterior I a b) hS
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentInterior_image_strictMono α.uliftMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexSet I) hiU)).trans
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponent_heq_of_set_eq s _ _ _ hcoord).trans
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplexData_hom_heq _ _ _ _ _ _ _ _ _).symm

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
