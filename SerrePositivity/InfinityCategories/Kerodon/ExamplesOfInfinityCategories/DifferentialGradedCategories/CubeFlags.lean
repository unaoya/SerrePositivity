module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Cube
public import Mathlib.GroupTheory.Perm.Sign

/-!
# 立方体の最大旗の単体

概要：座標の番号付けごとに、空集合から全体集合へ進む立方体の最大旗を作る。
方針：第 t 頂点を先頭 t 座標の集合とし、包含の関手として nerve の単体にする。
規約：番号付けは向きを指定する。Path の内部点には後で降順の番号付けを使う。
使われ方：HA 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の立方体の基本鎖の各項。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory
open scoped _root_.Simplicial

/-- 概要：番号付けられた座標の先頭 t 個を取る単調写像。
方針：番号が t 未満であるという条件を使う。
規約：零頂点は空集合、最後の頂点は全体集合。
使われ方：Kerodon 2.5.9（Tag 00SC） の立方体の最大旗。 -/
def cubeFlagOrder {T : Type u} {m : ℕ} (e : Fin m ≃ T) : Fin (m + 1) →o Set T where
  toFun t := {a | (e.symm a).val < t.val}
  monotone' := by
    intro s t h a ha
    change (e.symm a).val < s.val at ha
    change (e.symm a).val < t.val
    exact lt_of_lt_of_le ha h

/-- 概要：立方体の最大旗を nerve の m 単体として取る。
方針：先頭座標集合の単調写像を順序圏の関手にする。
規約：座標の型の宇宙を保つ。
使われ方：HA 1.3.1.16 の基本鎖を写像空間で評価する単体。 -/
def cubeFlag {T : Type u} {m : ℕ} (e : Fin m ≃ T) : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T) _⦋m⦌ :=
  (cubeFlagOrder e).monotone.functor

/-- 概要：最大旗の各頂点の所属は座標番号と頂点番号の大小で決まる。
方針：定義を評価する。
規約：包含方向に進む旗。
使われ方：Kerodon 2.5.9（Tag 00SC） の面の計算。 -/
lemma mem_cubeFlag_obj {T : Type u} {m : ℕ} (e : Fin m ≃ T)
    (t : Fin (m + 1)) (a : T) : a ∈ (cubeFlag e).obj t ↔ (e.symm a).val < t.val := Iff.rfl

/-- 概要：最大旗の最初の頂点は空集合である。
方針：自然数は零未満にならない。
規約：m=0 も含む。
使われ方：HA 1.3.1.16 の削除面の端点。 -/
lemma cubeFlag_obj_zero {T : Type u} {m : ℕ} (e : Fin m ≃ T) :
    (cubeFlag e).obj 0 = ∅ := by
  ext a
  change (e.symm a).val < 0 ↔ False
  exact iff_false_intro (Nat.not_lt_zero _)

/-- 概要：最大旗の最後の頂点は全体集合である。
方針：全ての座標番号が m 未満であることを使う。
規約：m=0 でも全体集合は空である。
使われ方：HA 1.3.1.16 の合成面の端点。 -/
lemma cubeFlag_obj_last {T : Type u} {m : ℕ} (e : Fin m ≃ T) :
    (cubeFlag e).obj (Fin.last m) = Set.univ := by
  ext a
  change (e.symm a).val < m ↔ True
  exact iff_true_intro (e.symm a).isLt

/-- 概要：最大旗は座標の番号付けの等式を保つ。
方針：番号付けの等式を置き換える。
規約：順序保存でない番号付けも許す。
使われ方：Kerodon 2.5.9（Tag 00SC） の置換の合成の比較。 -/
lemma cubeFlag_congr {T : Type u} {m : ℕ} {e f : Fin m ≃ T} (h : e = f) :
    cubeFlag e = cubeFlag f := congrArg cubeFlag h

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
