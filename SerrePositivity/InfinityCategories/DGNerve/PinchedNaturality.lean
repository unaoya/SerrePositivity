module
public import SerrePositivity.InfinityCategories.DGNerve.PinchedLinearEquiv
public import SerrePositivity.InfinityCategories.DGNerve.PinchedLinearReindex
public import SerrePositivity.InfinityCategories.DGNerve.PinchedReindexIndex

/-! # 右 pinched 単体の成分回収の自然性

概要：実際の単体の引き戻しによる回収族は、線形族の引き戻しに一致する。
方針：最終点固定延長の像と単射性を計算し、単射成分と潰れた零成分を比較する。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5。使われ方：面・退化の A 線形性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve.PinchedHom

open CategoryTheory DifferentialGraded
open scoped Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {x y : D}

/-- 概要：成分回収は任意の添字写像による引き戻しと可換。
方針：集合上単射なら像の成分、非単射なら三点以上の潰れた成分の零を比較する。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5。使われ方：線形模型と実際の単体の自然な比較。 -/
lemma toLinearData_pullback {m n : SimplexCategory}
    (s : (DGNerve.pinchedHom A D x y) _⦋n.len⦌) (α : m ⟶ n) :
    toLinearData (s.pullback α) = LinearData.pullback α.toOrderHom (toLinearData s) := by
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change k = 1 - (J.card : ℤ) at hk
  change (toLinearData (s.pullback α)).component J k hJ hk =
    (LinearData.pullback α.toOrderHom (toLinearData s)).component J k hJ hk
  apply eq_of_heq
  refine (toLinearData_component_heq (s.pullback α) J k hJ hk).trans ?_
  let θ := InfinityCategories.PinchedHom.extendOrderHom α.toOrderHom
  change HEq ((s.val.toSimplexData.pullback θ).hom (withLast J) (J.min' hJ).castSucc
    (Fin.last (m.len + 1)) k (two_withLast hJ) (min_withLast hJ _) (max_withLast J _)
    (by rw [card_withLast]; omega)) _
  by_cases hi : Set.InjOn α.toOrderHom (J : Set (Fin (m.len + 1)))
  · have hiθ : Set.InjOn θ (withLast J : Set (Fin (m.len + 2))) :=
      (injOn_extend_withLast_iff α.toOrderHom J).mpr hi
    rw [LinearData.pullback_component_of_inj _ _ _ _ _ _ hi,
      SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hiθ]
    have hdeg : k = 1 - ((J.image α.toOrderHom).card : ℤ) := by
      rw [Finset.card_image_of_injOn hi]
      exact hk
    refine HEq.trans ?_ (toLinearData_component_heq s (J.image α.toOrderHom) k
      (hJ.image α.toOrderHom) hdeg).symm
    apply s.val.toSimplexData.hom_heq_of_indices_degree
    · exact image_withLast_extend α.toOrderHom J
    · rw [InfinityCategories.PinchedHom.extendOrderHom_castSucc]
      exact congrArg Fin.castSucc (Index.image_min α.toOrderHom.monotone (J.isLeast_min' hJ) _)
    · exact InfinityCategories.PinchedHom.extendOrderHom_last _
    · rfl
  · have hiθ : ¬ Set.InjOn θ (withLast J : Set (Fin (m.len + 2))) :=
      mt (injOn_extend_withLast_iff α.toOrderHom J).mp hi
    have hc : (withLast J).card ≠ 2 := by
      have := two_of_not_injOn α.toOrderHom J hi
      rw [card_withLast]
      omega
    rw [LinearData.pullback_component_of_not_inj _ _ _ _ _ _ hi,
      SimplexData.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _ hiθ hc]
    change HEq (0 : GradedHom A (s.val.obj (θ (J.min' hJ).castSucc))
      (s.val.obj (θ (Fin.last (m.len + 1)))) k) (0 : GradedHom A x y k)
    dsimp only [θ]
    rw [InfinityCategories.PinchedHom.extendOrderHom_castSucc,
      InfinityCategories.PinchedHom.extendOrderHom_last, source_obj s _, target_obj s]

end SerrePositivity.InfinityCategories.DGNerve.PinchedHom
