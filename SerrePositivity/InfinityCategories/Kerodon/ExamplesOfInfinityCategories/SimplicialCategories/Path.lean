module

public import Mathlib.AlgebraicTopology.SimplicialNerve

/-!
# Coherent nerve の path の包含規約

概要：Mathlib の `SimplicialThickening.Path` を区間の内部点の部分集合で記述する。
方針：端点を取り除く写像と端点を付け直す写像を互いに逆にし、包含を比較する。
規約：path の射は包含方向。Kerodon 2.4.3.1（Tag 00KN） の逆包含とは向きが逆である。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.4（Tag 00LM）・2.4.5.8（Tag 00LR） の立方体と合成面の記述に使う。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

open CategoryTheory.SimplicialThickening

variable {J : Type u} [LinearOrder J] {a b c : J}

/-- 概要：path 間の射はその部分集合の包含と同値である。
方針：Mathlib の誘導圏の射から包含を取り出す。
規約：Kerodon 2.4.3.1（Tag 00KN） の逆包含と逆向き。
使われ方：立方体の座標順序を確認する。 -/
lemma path_hom_iff (p q : Path a b) : Nonempty (p ⟶ q) ↔ p.I ⊆ q.I := by
  exact ⟨fun ⟨f⟩ ↦ f.1.1.1, fun h ↦ ⟨⟨⟨⟨h⟩⟩⟩⟩⟩

/-- 概要：path の内部点を取り出す。
方針：部分集合を開区間へ制限する。
規約：座標が 1 とは点を含むこと。
使われ方：Kerodon 2.4.5.4（Tag 00LM） の Mathlib 規約での立方体座標。 -/
def pathInterior (p : Path a b) : Set (Set.Ioo a b) := {x | x.1 ∈ p.I}

/-- 概要：内部点の部分集合に両端点を加えて path を作る。
方針：端点か内部点かの三つの場合を用いる。
規約：a<b を明示する。
使われ方：Kerodon 2.4.5.4（Tag 00LM） の立方体座標の逆写像。 -/
def pathOfInterior (hab : a < b) (S : Set (Set.Ioo a b)) : Path a b where
  I := {x | x = a ∨ x = b ∨ ∃ h : x ∈ Set.Ioo a b, (⟨x, h⟩ : Set.Ioo a b) ∈ S}
  left := Or.inl rfl
  right := Or.inr (Or.inl rfl)
  left_le x hx := by
    rcases hx with rfl | rfl | ⟨hx, _⟩
    · exact le_rfl
    · exact hab.le
    · exact hx.1.le
  le_right x hx := by
    rcases hx with rfl | rfl | ⟨hx, _⟩
    · exact hab.le
    · exact le_rfl
    · exact hx.2.le

/-- 概要：端点の付加は内部点の集合を変えない。
方針：開区間では両端点の場合が不可能である。
規約：包含座標を用いる。
使われ方：Kerodon 2.4.5.4（Tag 00LM） の座標の全射性。 -/
@[simp]
lemma pathInterior_pathOfInterior (hab : a < b) (S : Set (Set.Ioo a b)) :
    pathInterior (pathOfInterior hab S) = S := by
  ext x
  change (x.1 = a ∨ x.1 = b ∨ ∃ h : x.1 ∈ Set.Ioo a b,
    (⟨x.1, h⟩ : Set.Ioo a b) ∈ S) ↔ x ∈ S
  simp [ne_of_gt x.2.1, ne_of_lt x.2.2]

/-- 概要：内部点の抽出と端点の付加で元の path を回収する。
方針：path 内の点が端点でなければ開区間内にある。
規約：a<b。
使われ方：Kerodon 2.4.5.4（Tag 00LM） の座標の単射性。 -/
@[simp]
lemma pathOfInterior_pathInterior (hab : a < b) (p : Path a b) :
    pathOfInterior hab (pathInterior p) = p := by
  apply Path.ext
  ext x
  constructor
  · rintro (rfl | rfl | ⟨_, hx⟩)
    · exact p.left
    · exact p.right
    · exact hx
  · intro hx
    by_cases ha : x = a
    · exact Or.inl ha
    by_cases hb : x = b
    · exact Or.inr (Or.inl hb)
    exact Or.inr (Or.inr ⟨⟨lt_of_le_of_ne (p.left_le x hx) (Ne.symm ha),
      lt_of_le_of_ne (p.le_right x hx) hb⟩, hx⟩)

/-- 概要：path と内部点の部分集合の間の全単射。
方針：内部点の抽出と端点の付加を組み合わせる。
規約：包含方向の座標であり補集合を取らない。
使われ方：Kerodon 2.4.5.4（Tag 00LM） の Hom 立方体の記述。 -/
def pathInteriorEquiv (hab : a < b) : Path a b ≃ Set (Set.Ioo a b) where
  toFun := pathInterior
  invFun := pathOfInterior hab
  left_inv := pathOfInterior_pathInterior hab
  right_inv := pathInterior_pathOfInterior hab

/-- 概要：内部点座標は path の包含を保存し反映する。
方針：端点はすべての path に共通である。
規約：逆包含にはしない。
使われ方：Kerodon 2.4.5.4（Tag 00LM） の立方体の順序比較。 -/
lemma pathInterior_subset_iff (p q : Path a b) :
    pathInterior p ⊆ pathInterior q ↔ p.I ⊆ q.I := by
  constructor
  · intro h x hx
    by_cases ha : x = a
    · exact ha ▸ q.left
    by_cases hb : x = b
    · exact hb ▸ q.right
    exact h (show (⟨x, ⟨lt_of_le_of_ne (p.left_le x hx) (Ne.symm ha),
      lt_of_le_of_ne (p.le_right x hx) hb⟩⟩ : Set.Ioo a b) ∈ pathInterior p from hx)
  · intro h x hx
    exact h hx

/-- 概要：path が内部の切断点を通れば前半へ制限できる。
方針：切断点以下の部分集合を取る。
規約：切断点は元の path に含まれる。
使われ方：Kerodon 2.4.4.16（Tag 00LF） の合成分解を包含規約で行う。 -/
def pathPrefix (p : Path a c) (b : J) (hb : b ∈ p.I) : Path a b where
  I := p.I ∩ Set.Iic b
  left := ⟨p.left, p.left_le b hb⟩
  right := ⟨hb, le_rfl⟩
  left_le x hx := p.left_le x hx.1
  le_right _ hx := hx.2

/-- 概要：path が内部の切断点を通れば後半へ制限できる。
方針：切断点以上の部分集合を取る。
規約：切断点は元の path に含まれる。
使われ方：Kerodon 2.4.4.16（Tag 00LF） の合成分解を包含規約で行う。 -/
def pathSuffix (p : Path a c) (b : J) (hb : b ∈ p.I) : Path b c where
  I := p.I ∩ Set.Ici b
  left := ⟨hb, le_rfl⟩
  right := ⟨p.right, p.le_right b hb⟩
  left_le _ hx := hx.2
  le_right x hx := p.le_right x hx.1

/-- 概要：前半と後半の path の合成は元の path に等しい。
方針：線形順序の全比較性で和集合を回収する。
規約：Mathlib の合成は和集合。
使われ方：Kerodon 2.4.5.8（Tag 00LR） の合成面上の貼合せ。 -/
lemma pathPrefix_comp_pathSuffix (p : Path a c) (b : J) (hb : b ∈ p.I) :
    @CategoryStruct.comp (SimplicialThickening J) _ (.mk a) (.mk b) (.mk c)
      (pathPrefix p b hb) (pathSuffix p b hb) = p := by
  apply Path.ext
  ext x
  change (x ∈ p.I ∧ x ≤ b) ∨ (x ∈ p.I ∧ b ≤ x) ↔ x ∈ p.I
  exact ⟨fun h ↦ h.elim And.left And.left, fun h ↦ (le_total x b).elim
    (fun hxb ↦ Or.inl ⟨h, hxb⟩) (fun hbx ↦ Or.inr ⟨h, hbx⟩)⟩

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
