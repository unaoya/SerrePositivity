module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentImageDegenerate

/-!
# 非単射な有限頂点集合の内部座標の重複

概要：三点以上の端点付き頂点集合で非単射な順序写像は、内部点を端点か別の内部点に重ねる。
方針：その二種類の重複がないと仮定し、端点の像と内部点の像を分離して単射性を復元する。
規約：元の頂点集合での最小・最大性だけを使う。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の非単射な引き戻しの零成分。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
variable {J K : Type u} [LinearOrder J] [LinearOrder K] {a b : J}

/-- 概要：三点以上の頂点集合上で非単射なら、内部点の像に端点か内部点との重複がある。
方針：内部点数が正であることを使い、二種類の重複を排除すると全頂点で単射となると示す。
規約：両端の像が一致する場合も内部点と端点の重複として検出する。
使われ方：Kerodon 2.5.9（Tag 00SC） の非単射分岐で退化する最大旗を選ぶ。 -/
lemma coherentInterior_collision_of_not_inj (f : J →o K) (I : Finset J)
    (ha : IsLeast (I : Set J) a) (hb : IsGreatest (I : Set J) b) (hab : a < b)
    (hcard : 2 < I.card) (hi : ¬ Set.InjOn f (I : Set J)) :
    (∃ t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentInteriorSet I a b, f t.val.val = f a ∨ f t.val.val = f b) ∨
      ∃ t w : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentInteriorSet I a b, t ≠ w ∧ f t.val.val = f w.val.val := by
  classical
  by_contra h
  have hE : ∀ t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentInteriorSet I a b, ¬ (f t.val.val = f a ∨ f t.val.val = f b) :=
    fun t ht ↦ h (Or.inl ⟨t, ht⟩)
  have hC : ∀ t w : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentInteriorSet I a b, t ≠ w → f t.val.val ≠ f w.val.val :=
    fun t w htw he ↦ h (Or.inr ⟨t, w, htw, he⟩)
  have habf : f a ≠ f b := by
    intro he
    have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_coherentInteriorSet ha hb hab
    obtain ⟨t, ht⟩ := Finset.card_pos.mp (show 0 < (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentInteriorSet I a b).card by omega)
    have hft : f t.val = f a := le_antisymm
      ((f.monotone t.property.2.le).trans_eq he.symm) (f.monotone t.property.1.le)
    exact hE ⟨t, ht⟩ (Or.inl hft)
  have hprea : ∀ x ∈ I, f x = f a → x = a := by
    intro x hx he
    by_cases hxa : x = a
    · exact hxa
    by_cases hxb : x = b
    · exact False.elim (habf (he.symm.trans (congrArg f hxb)))
    let t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentInteriorSet I a b :=
      ⟨⟨x, lt_of_le_of_ne (ha.2 hx) (Ne.symm hxa), lt_of_le_of_ne (hb.2 hx) hxb⟩,
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_coherentInteriorSet I a b _).mpr hx⟩
    exact False.elim (hE t (Or.inl he))
  have hpreb : ∀ x ∈ I, f x = f b → x = b := by
    intro x hx he
    by_cases hxb : x = b
    · exact hxb
    by_cases hxa : x = a
    · exact False.elim (habf ((congrArg f hxa).symm.trans he))
    let t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentInteriorSet I a b :=
      ⟨⟨x, lt_of_le_of_ne (ha.2 hx) (Ne.symm hxa), lt_of_le_of_ne (hb.2 hx) hxb⟩,
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_coherentInteriorSet I a b _).mpr hx⟩
    exact False.elim (hE t (Or.inr he))
  apply hi
  intro x hx y hy he
  by_cases hxa : x = a
  · subst x
    exact (hprea y hy he.symm).symm
  by_cases hxb : x = b
  · subst x
    exact (hpreb y hy he.symm).symm
  by_cases hya : y = a
  · subst y
    exact hprea x hx he
  by_cases hyb : y = b
  · subst y
    exact hpreb x hx he
  let t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentInteriorSet I a b :=
    ⟨⟨x, lt_of_le_of_ne (ha.2 hx) (Ne.symm hxa), lt_of_le_of_ne (hb.2 hx) hxb⟩,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_coherentInteriorSet I a b _).mpr hx⟩
  let w : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentInteriorSet I a b :=
    ⟨⟨y, lt_of_le_of_ne (ha.2 hy) (Ne.symm hya), lt_of_le_of_ne (hb.2 hy) hyb⟩,
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_coherentInteriorSet I a b _).mpr hy⟩
  by_contra hxy
  exact hC t w (fun htw ↦ hxy (congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentInteriorSet I a b ↦ z.val.val) htw)) he

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
