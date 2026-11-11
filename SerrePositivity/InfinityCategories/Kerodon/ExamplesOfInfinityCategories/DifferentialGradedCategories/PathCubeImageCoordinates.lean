module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentHomCoordinates

/-!
# 順序写像による有限内部座標の像

概要：選んだ有限内部座標が像でも内部にあり、その上で厳密単調なら、座標の像と順序同型になる。
方針：選んだ点の像を新しい開区間の部分型にし、その有限像への全単射を作る。
規約：順序写像の単射性は選んだ有限座標上だけに要求する。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の有限頂点集合上で単射な引き戻しの自然性。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
variable {J K : Type u} [LinearOrder J] [LinearOrder K] {a b : J}

/-- 概要：選んだ内部点の像を像の両端の間の有限内部座標にする。
方針：各点の内部性の証明を付け、全ての有限座標の像を取る。
規約：順序写像は全体で単射である必要はない。
使われ方：Kerodon 2.5.9（Tag 00SC） の単射な有限頂点集合の像の立方体。 -/
def pathCubeImageSet (f : J →o K) (S : Finset (Set.Ioo a b))
    (hS : ∀ t : S, f a < f t.val.val ∧ f t.val.val < f b) :
    Finset (Set.Ioo (f a) (f b)) :=
  Finset.univ.image (fun t : S ↦ (⟨f t.val.val, hS t⟩ : Set.Ioo (f a) (f b)))

/-- 概要：有限内部点上で厳密単調な写像はその有限像への順序同型を与える。
方針：像の所属で全射性を示し、厳密単調性で単射性と順序の反映を示す。
規約：像の座標の順序は元の像の順序集合から取る。
使われ方：HA 1.3.1.16 の降順の番号付けを像へ移す。 -/
def pathCubeImageIso (f : J →o K) (S : Finset (Set.Ioo a b))
    (hS : ∀ t : S, f a < f t.val.val ∧ f t.val.val < f b)
    (hf : StrictMono (fun t : S ↦ f t.val.val)) : S ≃o ↥(pathCubeImageSet f S hS) where
  toEquiv := Equiv.ofBijective
    (fun t ↦ ⟨⟨f t.val.val, hS t⟩, Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩⟩) (by
      constructor
      · intro t s h
        apply hf.injective
        exact congrArg (fun z : ↥(pathCubeImageSet f S hS) ↦ z.val.val) h
      · intro z
        obtain ⟨t, _, ht⟩ := Finset.mem_image.mp z.property
        exact ⟨t, Subtype.ext ht⟩)
  map_rel_iff' := by intro t s; exact hf.le_iff_le

/-- 概要：有限像の順序同型は各座標を元の順序写像の値に送る。
方針：順方向の定義を評価する。
規約：部分型の証明を忘れた元の値の等式。
使われ方：Kerodon 2.5.9（Tag 00SC） の Path の頂点集合の像の計算。 -/
lemma pathCubeImageIso_val (f : J →o K) (S : Finset (Set.Ioo a b))
    (hS : ∀ t : S, f a < f t.val.val ∧ f t.val.val < f b)
    (hf : StrictMono (fun t : S ↦ f t.val.val)) (t : S) :
    (pathCubeImageIso f S hS hf t).val.val = f t.val.val := rfl

/-- 概要：有限内部点上で厳密単調な写像は像の内部座標数を保つ。
方針：座標の順序同型で有限集合の濃度を比較する。
規約：次数は両側で同じになる。
使われ方：HA 1.3.1.16 の単射な引き戻しの次数の同定。 -/
lemma pathCubeImageSet_card (f : J →o K) (S : Finset (Set.Ioo a b))
    (hS : ∀ t : S, f a < f t.val.val ∧ f t.val.val < f b)
    (hf : StrictMono (fun t : S ↦ f t.val.val)) : (pathCubeImageSet f S hS).card = S.card := by
  simpa using (Fintype.card_congr (pathCubeImageIso f S hS hf).toEquiv).symm

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
