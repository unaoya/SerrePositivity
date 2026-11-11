module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.PathCubeComposition

/-!
# Path の有限内部点集合の区間への制限

概要：元の内部点の有限集合を別の開区間に制限し、その座標を順序同型で同定する。
方針：内部点を元の順序集合へ忘れてから区間の部分型へ戻す。
規約：新しい両端点は内部点として数えない。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の合成面の左右の有限座標集合。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
variable {J : Type u} [LinearOrder J] {a b : J}

/-- 概要：有限内部点集合のうち新しい開区間にある点の有限集合を作る。
方針：元の順序集合への像を取り、新しい開区間の部分型へ制限する。
規約：集合の型も新しい区間の型となる。
使われ方：Kerodon 2.5.9（Tag 00SC） の左右の小さい Path の立方体の座標。 -/
def pathIntervalSet (S : Finset (Set.Ioo a b)) (c d : J) : Finset (Set.Ioo c d) :=
  (S.image Subtype.val).subtype (fun t ↦ t ∈ Set.Ioo c d)

/-- 概要：区間に制限した有限集合への所属は元の値の像への所属である。
方針：有限集合の subtype の所属条件を評価する。
規約：新しい開区間の条件は点の型に含まれる。
使われ方：HA 1.3.1.16 の切断点の左右への座標の移送。 -/
lemma mem_pathIntervalSet (S : Finset (Set.Ioo a b)) (c d : J) (t : Set.Ioo c d) :
    t ∈ pathIntervalSet S c d ↔ t.val ∈ S.image Subtype.val := Finset.mem_subtype

/-- 概要：区間内の元の有限座標と区間に制限した有限集合の座標は順序同型である。
方針：元の値を保ったまま部分型の証明を付け替え、全単射性を示す。
規約：元の順序集合の値は変わらない。
使われ方：Kerodon 2.5.9（Tag 00SC） の左右の部分座標と小さい立方体の番号付けの比較。 -/
def pathIntervalCoordinateIso (S : Finset (Set.Ioo a b)) (c d : J) :
    {t : S // t.val.val ∈ Set.Ioo c d} ≃o ↥(pathIntervalSet S c d) where
  toEquiv := Equiv.ofBijective (fun t ↦ ⟨⟨t.val.val.val, t.property⟩,
    (mem_pathIntervalSet S c d _).mpr
      (Finset.mem_image.mpr ⟨t.val.val, t.val.property, rfl⟩)⟩) (by
    constructor
    · intro t s h
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : ↥(pathIntervalSet S c d) ↦ z.val.val) h
    · intro s
      obtain ⟨t, ht, he⟩ := Finset.mem_image.mp ((mem_pathIntervalSet S c d _).mp s.property)
      refine ⟨⟨⟨t, ht⟩, ?_⟩, ?_⟩
      · change t.val ∈ Set.Ioo c d
        rw [he]
        exact s.val.property
      · apply Subtype.ext
        apply Subtype.ext
        exact he)
  map_rel_iff' := by intro t s; rfl

/-- 概要：区間の座標の順序同型は元の点の値を保つ。
方針：順方向の定義を評価する。
規約：三重の部分型から元の順序集合へ値を取る。
使われ方：HA 1.3.1.16 の左右の Path の点集合の比較。 -/
lemma pathIntervalCoordinateIso_val (S : Finset (Set.Ioo a b)) (c d : J)
    (t : {t : S // t.val.val ∈ Set.Ioo c d}) :
    (pathIntervalCoordinateIso S c d t).val.val = t.val.val.val := rfl

/-- 概要：区間の座標の逆順序同型も元の点の値を保つ。
方針：順序同型の逆合成の等式で元の値を取る。
規約：元の有限集合に戻すときも点の値は同じ。
使われ方：Kerodon 2.5.9（Tag 00SC） の切断点の左右の座標から元の座標へ戻す。 -/
lemma pathIntervalCoordinateIso_symm_val (S : Finset (Set.Ioo a b)) (c d : J)
    (t : pathIntervalSet S c d) :
    ((pathIntervalCoordinateIso S c d).symm t).val.val.val = t.val.val :=
  congrArg (fun z : ↥(pathIntervalSet S c d) ↦ z.val.val)
    ((pathIntervalCoordinateIso S c d).apply_symm_apply t)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
