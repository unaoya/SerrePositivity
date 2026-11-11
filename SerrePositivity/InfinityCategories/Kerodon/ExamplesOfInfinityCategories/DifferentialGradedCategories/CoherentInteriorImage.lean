module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentImageNaturality

/-!
# 有限頂点集合上の単射性と内部座標の像

概要：有限頂点集合上で単射な順序写像は、内部座標を像の頂点集合の内部座標に同定する。
方針：有限集合上の単射性を厳密単調性へ変え、開区間の所属を像の前後で比較する。
規約：有限集合の外での単射性は要求しない。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の全ての単体作用に対する単射の場合。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
variable {J K : Type u} [LinearOrder J] [LinearOrder K] {a b : J}

/-- 概要：有限頂点集合上で単射なら、その内部点の像は像の両端の間にある。
方針：元の端点と内部点に有限集合上の厳密単調性を使う。
規約：最小・最大であることから端点の所属を得る。
使われ方：Kerodon 2.5.9（Tag 00SC） の像の内部座標の型を作る。 -/
lemma coherentInterior_image_bounds (f : J →o K) (I : Finset J)
    (ha : IsLeast (I : Set J) a) (hb : IsGreatest (I : Set J) b)
    (hi : Set.InjOn f (I : Set J)) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentInteriorSet I a b) :
    f a < f t.val.val ∧ f t.val.val < f b := by
  have hm : StrictMonoOn f (I : Set J) := (f.monotone.monotoneOn _).strictMonoOn_of_injOn hi
  have ht : t.val.val ∈ I := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_coherentInteriorSet I a b t.val).mp t.property
  exact ⟨hm ha.1 ht t.val.property.1, hm ht hb.1 t.val.property.2⟩

/-- 概要：有限頂点集合上の単射な順序写像はその内部座標上で厳密単調である。
方針：内部座標の所属を元の頂点集合への所属に戻す。
規約：部分型の順序は元の順序から得る。
使われ方：HA 1.3.1.16 の降順の番号付けの移送。 -/
lemma coherentInterior_image_strictMono (f : J →o K) (I : Finset J)
    (hi : Set.InjOn f (I : Set J)) :
    StrictMono (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentInteriorSet I a b ↦ f t.val.val) := by
  intro t s h
  exact (f.monotone.monotoneOn _).strictMonoOn_of_injOn hi
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_coherentInteriorSet I a b t.val).mp t.property)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_coherentInteriorSet I a b s.val).mp s.property) h

/-- 概要：内部座標の有限像は像の頂点集合の内部座標に等しい。
方針：像の内部点の原像を取り、端点でないことと最小・最大性から元の内部性を得る。
規約：像の端点は元の端点の像である。
使われ方：Kerodon 2.5.9（Tag 00SC） の dg 引き戻しの像の成分との同定。 -/
lemma coherentInteriorSet_image (f : J →o K) (I : Finset J)
    (ha : IsLeast (I : Set J) a) (hb : IsGreatest (I : Set J) b)
    (hi : Set.InjOn f (I : Set J)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeImageSet f (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentInteriorSet I a b)
      (coherentInterior_image_bounds f I ha hb hi) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentInteriorSet (I.image f) (f a) (f b) := by
  ext z
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pathCubeImageSet, Finset.mem_image, Finset.mem_univ, true_and,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_coherentInteriorSet]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t.val.val, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_coherentInteriorSet I a b t.val).mp t.property,
      congrArg Subtype.val ht⟩
  · rintro ⟨t, ht, he⟩
    have hat : a < t := lt_of_le_of_ne (ha.2 ht) (by
      intro h
      have h' : f a = z.val := by simpa [← h] using he
      exact (ne_of_gt z.property.1) h'.symm)
    have htb : t < b := lt_of_le_of_ne (hb.2 ht) (by
      intro h
      have h' : f b = z.val := by simpa [h] using he
      exact (ne_of_lt z.property.2) h'.symm)
    exact ⟨⟨⟨t, hat, htb⟩, (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mem_coherentInteriorSet I a b _).mpr ht⟩,
      Subtype.ext he⟩

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
