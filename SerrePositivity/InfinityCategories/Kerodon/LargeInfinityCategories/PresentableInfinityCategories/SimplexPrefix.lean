module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
概要：単体作用素に最小頂点を加える二つの明示的な操作。
方針：零頂点と後続頂点を分けて単調写像を構成する。
規約：元の単体作用素の後続頂点での値を保持する。
使われ方：反対単体圏の対角の comma の収縮関手。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open scoped _root_.Simplicial

/-- 概要：単体作用素の始域に最小頂点を加え、零頂点を零へ送る。
方針：後続頂点では元の単調写像を使う。
規約：終域の単体を変更しない。
使われ方：comma の対象に最小頂点を付け加える。 -/
def simplexPrefixCone {m n : SimplexCategory} (f : m ⟶ n) :
    ⦋m.len + 1⦌ ⟶ n :=
  SimplexCategory.mkHom {
    toFun := Fin.cases 0 (fun i ↦ f.toOrderHom i)
    monotone' := by
      intro i j hij
      cases i using Fin.cases with
      | zero => exact Fin.zero_le _
      | succ i =>
        cases j using Fin.cases with
        | zero => simp at hij
        | succ j => exact f.toOrderHom.monotone (Fin.succ_le_succ_iff.mp hij) }

/-- 概要：単体作用素の両端に最小頂点を加える。
方針：零は零へ、後続頂点は元の像の後続へ送る。
規約：後続部分で元の作用素を保持する。
使われ方：最小頂点を追加した comma の射の作用。 -/
def simplexPrefixMap {m n : SimplexCategory} (f : m ⟶ n) :
    ⦋m.len + 1⦌ ⟶ ⦋n.len + 1⦌ :=
  SimplexCategory.mkHom {
    toFun := Fin.cases 0 (fun i ↦ (f.toOrderHom i).succ)
    monotone' := by
      intro i j hij
      cases i using Fin.cases with
      | zero => exact Fin.zero_le _
      | succ i =>
        cases j using Fin.cases with
        | zero => simp at hij
        | succ j => exact Fin.succ_le_succ_iff.mpr (f.toOrderHom.monotone
            (Fin.succ_le_succ_iff.mp hij)) }

/-- 概要：最小頂点の追加は元の対象の恒等射を保つ。
方針：零と後続で座標を比較する。
規約：単体作用素の厳密な等式。
使われ方：収縮関手の恒等則。 -/
lemma simplexPrefixMap_id (m : SimplexCategory) : simplexPrefixMap (𝟙 m) = 𝟙 _ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  cases i using Fin.cases <;> rfl

/-- 概要：両端の最小頂点の追加は合成を保つ。
方針：零と後続で元の合成の座標を比較する。
規約：全ての単体作用素を扱う。
使われ方：収縮関手の合成則。 -/
lemma simplexPrefixMap_comp {a b c : SimplexCategory} (f : a ⟶ b) (g : b ⟶ c) :
    simplexPrefixMap (f ≫ g) = simplexPrefixMap f ≫ simplexPrefixMap g := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  cases i using Fin.cases <;> rfl

/-- 概要：始域だけへの最小頂点の追加は、両端への追加と合成に整合する。
方針：零と後続で元の合成を計算する。
規約：終域は元の単体に固定する。
使われ方：対角 comma の可換三角形の保存。 -/
lemma simplexPrefixMap_comp_cone {a b c : SimplexCategory} (f : a ⟶ b) (g : b ⟶ c) :
    simplexPrefixMap f ≫ simplexPrefixCone g = simplexPrefixCone (f ≫ g) := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  cases i using Fin.cases <;> rfl

/-- 概要：元の単体を最小頂点の後の部分へ入れる。
方針：各頂点を後続へ送る。
規約：頂点の順序を保持する。
使われ方：収縮関手から恒等関手への自然変換。 -/
def simplexPrefixTail (m : SimplexCategory) : m ⟶ ⦋m.len + 1⦌ :=
  SimplexCategory.mkHom {
    toFun := Fin.succ
    monotone' := fun _ _ h ↦ Fin.succ_le_succ_iff.mpr h }

/-- 概要：最小頂点の後の部分で元の単体作用素を回収する。
方針：各元の頂点で定義を計算する。
規約：作用素の厳密な等式。
使われ方：恒等関手への自然変換の comma 条件。 -/
lemma simplexPrefixTail_comp_cone {m n : SimplexCategory} (f : m ⟶ n) :
    simplexPrefixTail m ≫ simplexPrefixCone f = f := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  rfl

/-- 概要：後続部分への包含は最小頂点を加える関手に関して自然。
方針：各頂点で元の像の後続を比較する。
規約：全単体作用素に適用する。
使われ方：恒等関手への自然変換の自然性。 -/
lemma simplexPrefixTail_naturality {m n : SimplexCategory} (f : m ⟶ n) :
    simplexPrefixTail m ≫ simplexPrefixMap f = f ≫ simplexPrefixTail n := by
  apply SimplexCategory.Hom.ext
  rfl

/-- 概要：新しい最小頂点は全単体作用素で最小頂点へ送られる。
方針：零頂点の定義を計算する。
規約：元の作用素の像に依存しない。
使われ方：定値関手への自然変換の自然性。 -/
lemma simplexPrefixMap_zero {m n : SimplexCategory} (f : m ⟶ n) :
    SimplexCategory.const ⦋0⦌ ⦋m.len + 1⦌ 0 ≫ simplexPrefixMap f =
      SimplexCategory.const ⦋0⦌ ⦋n.len + 1⦌ 0 := by
  apply SimplexCategory.Hom.ext
  rfl

/-- 概要：始域に加えた最小頂点は元の終域の最小頂点へ送られる。
方針：零頂点で定義を計算する。
規約：元の終域を保持する。
使われ方：定値関手への自然変換の comma 条件。 -/
lemma simplexPrefixCone_zero {m n : SimplexCategory} (f : m ⟶ n) :
    SimplexCategory.const ⦋0⦌ ⦋m.len + 1⦌ 0 ≫ simplexPrefixCone f =
      SimplexCategory.const ⦋0⦌ n 0 := by
  apply SimplexCategory.Hom.ext
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
