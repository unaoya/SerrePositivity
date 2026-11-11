module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentNoninjectiveInterior

/-!
# 比較成分の非単射な高次引き戻し

概要：三点以上の頂点集合上で非単射な引き戻しは、coherent 比較成分でも零になる。
方針：内部座標の像の重複を検出し、全ての最大旗の退化で立方体評価を零にする。
規約：二点集合が潰れる場合の単位成分は別に扱う。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の比較写像の高次の非単射分岐。

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

/-- 概要：三点以上の有限頂点集合上で非単射な順序写像による coherent 成分は零である。
方針：内部点と端点または内部点どうしの重複に分け、全旗の評価を零にする。
規約：通常の線形順序集合上の native な豊穣関手について述べる。
使われ方：Kerodon 2.5.9（Tag 00SC） の dg 単体の高次の非単射分岐。 -/
lemma coherentCubeComponent_image_zero_of_not_inj
    {J K : Type u} [LinearOrder J] [LinearOrder K] {a b : J}
    (s : EnrichedFunctor SSet (SimplicialThickening K) (ClosedCategory R D))
    (f : J →o K) (I : Finset J) (ha : IsLeast (I : Set J) a)
    (hb : IsGreatest (I : Set J) b) (hab : a < b) (hcard : 2 < I.card)
    (hi : ¬ Set.InjOn f (I : Set J)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponent ((SimplicialThickening.functor f).comp SSet s)
      hab (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentInteriorSet I a b) = 0 := by
  rcases _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentInterior_collision_of_not_inj f I ha hb hab hcard hi with hE | hC
  · obtain ⟨t, ht⟩ := hE
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation_coherentImage_zero_of_endpoint s f hab _ _ t ht
  · obtain ⟨t, w, htw, he⟩ := hC
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation_coherentImage_zero_of_collision s f hab _ _ t w htw he

/-- 概要：二点以外の非単射な引き戻しでは比較成分族と dg 引き戻しの hom が等しい。
方針：持ち上げた頂点集合の非単射性を確認し、両側の成分が零であることを使う。
規約：既存の hom の端点・次数の証明をそのまま使う。
使われ方：HA 1.3.1.16 の比較写像の自然性の高次の非単射分岐。 -/
lemma coherentSimplexData_pullback_hom_of_not_inj {m n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := R) (D := D)) _⦋n⦌)
    (α : Fin (m + 1) →o Fin (n + 1)) (I : Finset (Fin (m + 1)))
    (a b : Fin (m + 1)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ))
    (hi : ¬ Set.InjOn α (I : Set _)) (hc : I.card ≠ 2) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplexData ((SimplicialThickening.functor α.uliftMap).comp SSet s)).hom
      I a b k hI ha hb hk =
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplexData s).pullback α).hom I a b k hI ha hb hk := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _ hi hc]
  have ha₀ : IsLeast (I : Set _) a := by rw [ha]; exact I.isLeast_min' _
  have hb₀ : IsGreatest (I : Set _) b := by rw [hb]; exact I.isGreatest_max' _
  have hab : a < b := by rw [ha, hb]; exact I.min'_lt_max'_of_card (by omega)
  have hiU : ¬ Set.InjOn α.uliftMap ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexSet.{u} I) : Set _) := by
    intro h
    apply hi
    intro x hx y hy he
    have hxy := h (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      (Finset.mem_image.mpr ⟨y, hy, rfl⟩) (congrArg ULift.up he)
    exact congrArg ULift.down hxy
  have hzero := coherentCubeComponent_image_zero_of_not_inj s α.uliftMap
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexSet.{u} I) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexSet_isLeast ha₀)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexSet_isGreatest hb₀)
    (show (ULift.up a : ULift.{u} (Fin (m + 1))) < ULift.up b from hab)
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexSet_card]; omega) hiU
  have hdeg : k = -((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexInterior.{u} I a b).card : ℤ) := by
    have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexInterior_card.{u} ha₀ hb₀ hab
    omega
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplexData_hom_eq_componentAt _ I a b k hI ha hb hk hab hdeg]
  cases hdeg
  exact hzero

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
