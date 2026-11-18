module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CanonicalSequence
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CanonicalWordMoves
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CaesuraGaps
public import SerrePositivity.EInfinity.BarrattEccles.Nondegenerate

/-!
模型。文献の定義との比較は後で
# 標準頂点列の隣接行の移動と非退化性

概要：Berger–Fresse §1.4.2–3 の復元した実際の BE 単体の非退化性を証明する。
方針：行内部の不変性と行末の一文字の移動を各行開始位置へ接続する。
規約：基礎環に依存せず、元の語の非退化性だけを使う。
使われ方：全射語ごとに正規化 BE 複体の基底の候補を指定する。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
open scoped _root_.Simplicial

/-- 概要：行の開始位置と区切りでの復元行は同じ（BF §1.4.2）。
方針：その間に別の区切りがないことから区間不変性を使う。
規約：最後の行を除く各行に適用する。
使われ方：区切りでの一文字の移動を標準頂点間へ移す。 -/
lemma canonicalRow_start_eq_cut {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (i : Fin d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow (List.ofFn v.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.castSucc) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow (List.ofFn v.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i).val := by
  symm
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow_word_eq_of_no_caesura v _ _ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart_le_caesuraAt v i)
    (Nat.le_of_lt (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i).isLt)
  exact fun k hs hc => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.not_caesura_between_start_and_cut v i k hs hc

/-- 概要：標準頂点の二つの行は非自明な一文字の移動で結ばれる（BF §1.4.2–3）。
方針：行末の移動の式を行開始位置の行に置き換える。
規約：移動する文字は指定した区切りの値。
使われ方：TR の行長の選択を強制する境界重複の証明に用いる。 -/
lemma canonicalRows_adjacent_exists_move {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (i : Fin d) :
    ∃ pre left right : List (Fin n),
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow (List.ofFn v.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.castSucc) =
        pre ++ [v.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i)] ++ left ++ right ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow (List.ofFn v.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i.succ) =
        pre ++ left ++ [v.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i)] ++ right ∧
      left ≠ [] ∧ v.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i) ∉ left ∧ v.val (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt v i) ∉ right := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow_start_eq_cut, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart_succ_eq_caesuraAt]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow_word_exists_move v _ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt_caesura v i)

/-- 概要：標準頂点列の隣接頂点は常に異なる（BF §1.4.2–3）。
方針：頂点が同じなら逆置換の行も同じとなり、区切りでの非自明な変化に反する。
規約：零 arity・次数零では添字条件は空。
使われ方：復元した BE 単体の非退化性を示す。 -/
lemma canonicalVertices_ne_adjacent {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (i : Fin d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalVertices v i.castSucc ≠ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalVertices v i.succ := by
  intro he
  have hl := congrArg (fun σ : Equiv.Perm (Fin n) => List.ofFn (fun j => σ⁻¹ j)) he
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalVertices, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalPermutation_inv_list] at hl
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow_start_eq_cut, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart_succ_eq_caesuraAt] at hl
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow_word_ne_succ_of_caesura v _ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.caesuraAt_caesura v i) hl

/-- 概要：全射語から復元した BE 単体は非退化（BF §1.4.2–3）。
方針：隣接する頂点置換の非一致による BE 非退化性の特徴づけを使う。
規約：元の語の非退化性は Word の条件から得る。
使われ方：正規化 BE 基底の実際の添字として復元単体を使える。 -/
lemma canonicalSimplex_mem_nonDegenerate {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalSimplex v ∈ (_root_.SerrePositivity.EInfinity.BarrattEccles.simplicial n).nonDegenerate d := by
  rw [_root_.SerrePositivity.EInfinity.BarrattEccles.mem_nonDegenerate_iff, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.simplexEquiv_canonicalSimplex]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalVertices_ne_adjacent v

/-- 概要：全射語に対応する非退化 BE 単体（BF §1.4.2–3）。
方針：復元した単体とその非退化性を束ねる。
規約：TR が元の語になる等式はまだ後続の工程。
使われ方：TR の線形写像の全射性で基底元の逆像を指定する。 -/
def canonicalNondegenerateSimplex {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) :
    (_root_.SerrePositivity.EInfinity.BarrattEccles.simplicial n).nonDegenerate d :=
  ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalSimplex v, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalSimplex_mem_nonDegenerate v⟩

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
