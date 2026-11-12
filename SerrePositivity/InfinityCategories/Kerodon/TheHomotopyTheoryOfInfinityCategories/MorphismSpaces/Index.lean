module
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.Data.Fin.Tuple.Basic

/-! # 右 pinched Hom の添字写像

概要：単体の添字写像を最終頂点を固定する写像へ延ばす。
方針：先頭の頂点には元の写像を使い、追加した最終頂点は最終頂点へ送る。
規約：Kerodon §4.6.5（Tag 01KW）、右 pinched 写像空間。使われ方：面と退化の統一的な定義。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

open CategoryTheory Opposite
open scoped _root_.Simplicial

/-- 概要：添字の単調写像を最終頂点を固定する単調写像へ延ばす。
方針：先頭では元の写像、最終点では追加した最終点を取る。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：右 pinched Hom の引き戻し。 -/
def extendOrderHom {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) :
    Fin (m + 2) →o Fin (n + 2) where
  toFun := Fin.lastCases (Fin.last (n + 1)) (fun i => (α i).castSucc)
  monotone' := by
    intro a b hab
    induction a using Fin.lastCases with
    | last =>
      have hb : b = Fin.last (m + 1) := le_antisymm (Fin.le_last _) hab
      subst b
      exact le_rfl
    | cast a =>
      induction b using Fin.lastCases with
      | last =>
        simpa only [Fin.lastCases_castSucc, Fin.lastCases_last] using Fin.le_last (α a).castSucc
      | cast b =>
        simpa only [Fin.lastCases_castSucc, Fin.castSucc_le_castSucc_iff] using
          α.monotone (Fin.castSucc_le_castSucc_iff.mp hab)

/-- 概要：延長写像は先頭の頂点で元の写像と一致する。
方針：最終点分岐の定義を評価する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：先頭の面の定値条件。 -/
lemma extendOrderHom_castSucc {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (i : Fin (m + 1)) : extendOrderHom α i.castSucc = (α i).castSucc := by
  simp [extendOrderHom]

/-- 概要：延長写像は最終頂点を最終頂点へ送る。
方針：最終点分岐の定義を評価する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：終端条件の保存。 -/
lemma extendOrderHom_last {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) :
    extendOrderHom α (Fin.last (m + 1)) = Fin.last (n + 1) := by
  simp [extendOrderHom]

/-- 概要：単体圏の射を最終頂点を固定する射へ延ばす。
方針：単調写像の延長を単体圏の射として読む。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：右 pinched Hom の単体的構造。 -/
def extend {m n : SimplexCategory} (α : m ⟶ n) : ⦋m.len + 1⦌ ⟶ ⦋n.len + 1⦌ :=
  SimplexCategory.mkHom (extendOrderHom α.toOrderHom)

/-- 概要：先頭の面の包含。
方針：最終頂点以外の頂点を同じ番号へ送る。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：先頭の面全体を x に固定する条件。 -/
def front (n : ℕ) : ⦋n⦌ ⟶ ⦋n + 1⦌ :=
  SimplexCategory.mkHom Fin.castSuccOrderEmb.toOrderHom

/-- 概要：最終頂点を選ぶ射。
方針：零単体から追加した頂点への定値写像を取る。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：終端 y の条件。 -/
def lastVertex (n : ℕ) : ⦋0⦌ ⟶ ⦋n + 1⦌ :=
  SimplexCategory.const _ _ (Fin.last (n + 1))

/-- 概要：先頭面の包含と延長写像は可換。
方針：各先頭頂点で延長写像を計算する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：先頭面の条件の引き戻し。 -/
lemma front_extend {m n : SimplexCategory} (α : m ⟶ n) :
    front m.len ≫ extend α = α ≫ front n.len := by
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro i
  exact extendOrderHom_castSucc α.toOrderHom i

/-- 概要：延長写像は最終頂点を選ぶ射と可換。
方針：最終点での延長写像を計算する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：終端条件の引き戻し。 -/
lemma lastVertex_extend {m n : SimplexCategory} (α : m ⟶ n) :
    lastVertex m.len ≫ extend α = lastVertex n.len := by
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro i
  exact extendOrderHom_last α.toOrderHom

/-- 概要：最終頂点を固定する延長は恒等射を保つ。
方針：先頭の頂点と最終点で評価する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：単体的恒等則。 -/
lemma extend_id (n : SimplexCategory) : extend (𝟙 n) = 𝟙 ⦋n.len + 1⦌ := by
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro i
  induction i using Fin.lastCases with
  | last => exact extendOrderHom_last _
  | cast i => exact extendOrderHom_castSucc _ i

/-- 概要：最終頂点を固定する延長は合成を保つ。
方針：先頭の頂点と最終点で両辺の値を比較する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：単体的合成則。 -/
lemma extend_comp {l m n : SimplexCategory} (α : l ⟶ m) (β : m ⟶ n) :
    extend (α ≫ β) = extend α ≫ extend β := by
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro i
  induction i using Fin.lastCases with
  | last => simp [extend, extendOrderHom]
  | cast i => simp [extend, extendOrderHom]

/-- 概要：先頭面の包含は最終頂点を飛ばす面写像。
方針：各頂点で最終点を飛ばす写像を計算する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：通常の面写像による端点の記述。 -/
lemma front_eq_δ (n : ℕ) : front n = SimplexCategory.δ (Fin.last (n + 1)) := by
  apply SimplexCategory.Hom.ext
  apply DFunLike.ext
  intro i
  exact (Fin.succAbove_last_apply i).symm

/-- 概要：零次の先頭面は一単体の一番目の面。
方針：先頭面を最終点を飛ばす面と同定し、二頂点の場合を評価する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：右 pinched Hom の頂点と辺の比較。 -/
lemma front_zero : front 0 = SimplexCategory.δ (1 : Fin 2) := by
  rw [front_eq_δ, show Fin.last (0 + 1) = (1 : Fin 2) from by decide]

/-- 概要：零次の最終頂点は一単体の零番目の面で選ばれる。
方針：零単体の唯一の頂点で計算する。
規約：Kerodon §4.6.5（Tag 01KW）。使われ方：右 pinched Hom の頂点と辺の比較。 -/
lemma lastVertex_zero : lastVertex 0 = SimplexCategory.δ (0 : Fin 2) := by
  ext i
  fin_cases i
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
