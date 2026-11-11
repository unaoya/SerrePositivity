module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CubeLowDimensional
public import Mathlib.GroupTheory.Perm.Fin

/-!
# 立方体の番号付き座標面

概要：座標を一つ除いた立方体から、指定座標を 0 または 1 に固定した面へ写す。
方針：succAbove で残りの座標を埋め込み、1 面では固定座標を付け加える。
規約：小さい立方体の座標を ULift して元の立方体の宇宙を保つ。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の最大旗の外側の面の同定。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory
open scoped _root_.Simplicial

/-- 概要：一つ除いた座標を元の番号付けへ埋め込む。
方針：succAbove で固定座標を飛ばす。
規約：元の立方体と座標の宇宙を合わせる。
使われ方：Kerodon 2.5.9（Tag 00SC） の座標面の埋め込み。 -/
def cubeFaceEmbedding {T : Type u} {m : ℕ} (e : Fin (m + 1) ≃ T) (i : Fin (m + 1)) :
    ULift.{u} (Fin m) → T := fun a ↦ e (i.succAbove a.down)

/-- 概要：残りの座標集合を指定座標の 0 面または 1 面へ送る単調写像。
方針：座標の像を取り、1 面では固定座標を追加する。
規約：ε=false が削除面、ε=true が座標を含む面。
使われ方：HA 1.3.1.16 の立方体の境界。 -/
def cubeFaceOrder {T : Type u} {m : ℕ} (e : Fin (m + 1) ≃ T) (i : Fin (m + 1))
    (ε : Bool) : Set (ULift.{u} (Fin m)) →o Set T where
  toFun U := if ε then insert (e i) (cubeFaceEmbedding e i '' U) else cubeFaceEmbedding e i '' U
  monotone' := by
    intro U V h a ha
    cases ε with
    | false => exact Set.image_mono h ha
    | true => exact (Set.insert_subset_insert (Set.image_mono h)) ha

/-- 概要：座標面の包含を単体集合の射にする。
方針：座標集合の単調写像の nerve を取る。
規約：小さい立方体の宇宙も u。
使われ方：Kerodon 2.5.9（Tag 00SC） の基本鎖の境界の座標面への移送。 -/
def cubeFaceMap {T : Type u} {m : ℕ} (e : Fin (m + 1) ≃ T) (i : Fin (m + 1))
    (ε : Bool) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube (ULift.{u} (Fin m)) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T :=
  nerveMap (cubeFaceOrder e i ε).monotone.functor

/-- 概要：固定した座標は 1 面にだけ属する。
方針：succAbove の像が固定点を避けることを使う。
規約：任意の残りの座標集合で成立する。
使われ方：Kerodon 2.5.9（Tag 00SC） の座標面の固定座標の検査。 -/
lemma cubeFaceOrder_mem_fixed {T : Type u} {m : ℕ} (e : Fin (m + 1) ≃ T)
    (i : Fin (m + 1)) (ε : Bool) (U : Set (ULift.{u} (Fin m))) :
    e i ∈ cubeFaceOrder e i ε U ↔ ε = true := by
  have h : e i ∉ cubeFaceEmbedding e i '' U := by
    rintro ⟨a, _, ha⟩
    exact Fin.succAbove_ne i a.down (e.injective ha)
  cases ε <;> simp [cubeFaceOrder, h]

/-- 概要：固定点以外の座標の面への所属は元の小さい立方体の所属である。
方針：番号付けと succAbove の単射性で像の逆像を一意に決める。
規約：0 面と 1 面の両方に同じ式を使う。
使われ方：HA 1.3.1.16 の外側の面の最大旗の比較。 -/
lemma cubeFaceOrder_mem_succAbove {T : Type u} {m : ℕ} (e : Fin (m + 1) ≃ T)
    (i : Fin (m + 1)) (ε : Bool) (U : Set (ULift.{u} (Fin m))) (j : Fin m) :
    e (i.succAbove j) ∈ cubeFaceOrder e i ε U ↔ ULift.up j ∈ U := by
  have he : e (i.succAbove j) ≠ e i := fun h ↦ Fin.succAbove_ne i j (e.injective h)
  have h : e (i.succAbove j) ∈ cubeFaceEmbedding e i '' U ↔ ULift.up j ∈ U := by
    constructor
    · rintro ⟨a, ha, h⟩
      have ha' : a = ULift.up j := ULift.ext (i.succAboveOrderEmb.injective (e.injective h))
      exact ha' ▸ ha
    · intro hj
      exact ⟨ULift.up j, hj, rfl⟩
  cases ε <;> simpa [cubeFaceOrder, he] using h

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
