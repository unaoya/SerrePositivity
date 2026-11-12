module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentInteriorImage

/-!
# 持ち上げた有限頂点集合の像

概要：頂点番号の像と native な ULift の頂点の像を同定し、有限集合上の単射性を移す。
方針：二つの有限像の合成を展開し、ULift.down で等式を元の頂点番号へ戻す。
規約：像は元の単体の宇宙 u の中で取る。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の比較単体の自然性。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-- 概要：持ち上げた頂点集合の像は頂点番号の像の持ち上げに等しい。
方針：有限集合の像の合成を一つの像に直す。
規約：端点を含めて全ての選んだ頂点を移す。
使われ方：Kerodon 2.5.9（Tag 00SC） の像の内部座標集合の同定。 -/
lemma coherentVertexSet_image {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (I : Finset (Fin (m + 1))) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexSet.{u} I).image α.uliftMap = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexSet.{u} (I.image α) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexSet
  rw [Finset.image_image, Finset.image_image]
  rfl

/-- 概要：有限頂点番号上の単射性は native な持ち上げた頂点集合上でも成立する。
方針：所属を元の有限頂点集合へ戻し、像の等式を ULift.down で比較する。
規約：持ち上げる宇宙は単体的 Hom の宇宙とそろえる。
使われ方：HA 1.3.1.16 の有限内部座標の厳密単調性。 -/
lemma coherentVertexSet_injOn {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (I : Finset (Fin (m + 1))) (hi : Set.InjOn α (I : Set _)) :
    Set.InjOn (α.uliftMap : ULift.{u} (Fin (m + 1)) →o ULift.{u} (Fin (n + 1)))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexSet.{u} I) : Set _) := by
  intro x hx y hy h
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
  exact congrArg ULift.up (hi ha hb (congrArg ULift.down h))

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
