module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Simplicial.NecklaceBooleanCube

/-! # 元の necklace 写像の Bool 座標作用
概要：元の部分集合像を非 joint 座標へ移し、同じ全頂点作用から各座標を回収する。
方針：元の順序同型で像写像を移送し、恒等・合成と有限ファイバー表示を証明する。
規約：定数一となる joint の像も保持。使われ方：既存の max connection 圏への接続。
-/
@[expose] public section
universe u
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Simplicial
open SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の非 joint 座標の Bool 立方体間の、同じ部分集合像による作用。 -/
def necklaceBooleanMap {T U : _root_.SerrePositivity.InfinityCategories.Simplicial.Necklace.{u}} (f : T ⟶ U) :
    (T.down.NonjointVertex → Bool) →o (U.down.NonjointVertex → Bool) where
  toFun b := U.down.cubeSubsetBits (_root_.SerrePositivity.InfinityCategories.Simplicial.necklaceSubsetMap f (T.down.cubeSubsetFromBits b))
  monotone' _ _ h := U.down.cubeSubsetBits_monotone
    ((_root_.SerrePositivity.InfinityCategories.Simplicial.necklaceSubsetMap f).monotone (T.down.cubeSubsetFromBits_monotone h))

/-- 元の necklace の Bool 座標作用は恒等写像を保つ。 -/
lemma necklaceBooleanMap_id (T : _root_.SerrePositivity.InfinityCategories.Simplicial.Necklace.{u}) : _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceBooleanMap (𝟙 T) = OrderHom.id := by
  apply DFunLike.ext
  intro b
  change T.down.cubeSubsetBits (_root_.SerrePositivity.InfinityCategories.Simplicial.necklaceSubsetMap (𝟙 T) (T.down.cubeSubsetFromBits b)) = b
  rw [_root_.SerrePositivity.InfinityCategories.Simplicial.necklaceSubsetMap_id]
  exact T.down.cubeSubsetBits_fromBits b

/-- 元の necklace の Bool 座標作用は元の合成を保つ。 -/
lemma necklaceBooleanMap_comp {T U V : _root_.SerrePositivity.InfinityCategories.Simplicial.Necklace.{u}} (f : T ⟶ U) (g : U ⟶ V) :
    _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceBooleanMap (f ≫ g) = (_root_.SerrePositivity.InfinityCategories.Simplicial.necklaceBooleanMap g).comp (_root_.SerrePositivity.InfinityCategories.Simplicial.necklaceBooleanMap f) := by
  apply DFunLike.ext
  intro b
  change V.down.cubeSubsetBits
      (_root_.SerrePositivity.InfinityCategories.Simplicial.necklaceSubsetMap (f ≫ g) (T.down.cubeSubsetFromBits b)) =
    V.down.cubeSubsetBits (_root_.SerrePositivity.InfinityCategories.Simplicial.necklaceSubsetMap g (U.down.cubeSubsetFromBits
      (U.down.cubeSubsetBits (_root_.SerrePositivity.InfinityCategories.Simplicial.necklaceSubsetMap f (T.down.cubeSubsetFromBits b)))))
  rw [_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.cubeSubsetFromBits_bits, _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceSubsetMap_comp]
  rfl

/-- 元の出力座標が真であることは、同じ頂点ファイバーに真の入力があること。 -/
lemma necklaceBooleanMap_true_iff {T U : _root_.SerrePositivity.InfinityCategories.Simplicial.Necklace.{u}} (f : T ⟶ U)
    (b : T.down.NonjointVertex → Bool) (v : U.down.NonjointVertex) :
    _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceBooleanMap f b v = true ↔
      ∃ j : T.down.Vertex, T.down.cubeFullBits b j = true ∧ _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceVertexMap f j = v.val := by
  change decide (v.val ∈ (T.down.cubeSubsetFromBits b).val.image (_root_.SerrePositivity.InfinityCategories.Simplicial.necklaceVertexMap f)) =
    true ↔ _
  simp only [decide_eq_true_eq, Finset.mem_image, _root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.cubeSubsetFromBits,
    Finset.mem_filter, Finset.mem_univ, true_and]

/-- 元の出力は、joint の像による定数一と、非 joint ファイバーの max から回収される。 -/
lemma necklaceBooleanMap_coordinate {T U : _root_.SerrePositivity.InfinityCategories.Simplicial.Necklace.{u}} (f : T ⟶ U)
    (b : T.down.NonjointVertex → Bool) (v : U.down.NonjointVertex) :
    _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceBooleanMap f b v = true ↔
      (∃ j : T.down.Vertex, j.val ∈ T.down.joints ∧ _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceVertexMap f j = v.val) ∨
        ∃ j : T.down.NonjointVertex, b j = true ∧ _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceVertexMap f j.val = v.val := by
  rw [_root_.SerrePositivity.InfinityCategories.Simplicial.necklaceBooleanMap_true_iff]
  constructor
  · rintro ⟨j, hj, hfj⟩
    by_cases h : j.val ∈ T.down.joints
    · exact Or.inl ⟨j, h, hfj⟩
    · refine Or.inr ⟨⟨j, h⟩, ?_, hfj⟩
      simpa only [_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.cubeFullBits, dite_eq_right h] using hj
  · rintro (⟨j, hj, hfj⟩ | ⟨j, hj, hfj⟩)
    · exact ⟨j, by simp [_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.cubeFullBits, hj], hfj⟩
    · refine ⟨j.val, ?_, hfj⟩
      simpa only [_root_.SerrePositivity.InfinityCategories.Simplicial.NecklaceShape.cubeFullBits, dite_eq_right j.property] using hj

/-- 異なる出力頂点の順序は、元の全ファイバーの頂点順序を分離する。 -/
lemma necklaceVertexMap_orderedFibers {T U : _root_.SerrePositivity.InfinityCategories.Simplicial.Necklace.{u}} (f : T ⟶ U)
    (a b : T.down.Vertex) (h : _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceVertexMap f a < _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceVertexMap f b) : a < b := by
  by_contra hab
  have hba : b ≤ a := le_of_not_gt hab
  exact (not_le_of_gt h) (_root_.SerrePositivity.InfinityCategories.Simplicial.necklaceVertexMap_monotone f hba)

end SerrePositivity.InfinityCategories.Simplicial

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceBooleanMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceBooleanMap := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceBooleanMap

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceBooleanMap_comp := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceBooleanMap_comp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceBooleanMap_coordinate := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceBooleanMap_coordinate

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceBooleanMap_id := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceBooleanMap_id

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceBooleanMap_true_iff := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceBooleanMap_true_iff

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceVertexMap_orderedFibers := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceVertexMap_orderedFibers

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.necklaceBooleanMap._proof_1 := _root_.SerrePositivity.InfinityCategories.Simplicial.necklaceBooleanMap._proof_1
