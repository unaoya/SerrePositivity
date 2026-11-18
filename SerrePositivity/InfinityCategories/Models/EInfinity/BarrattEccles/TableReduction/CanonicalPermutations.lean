module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CanonicalRows
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Words

/-!
模型。文献の定義との比較は後で
# 全射語の各位置からの頂点置換の復元

概要：Berger–Fresse §1.4.2 の復元する行を実際の対称群の元へ変換する。
方針：行の重複のなさと全値の存在から有限添字の同値を構成する。
規約：BE の位置の作用に合わせて値の一行表示の逆置換を返す。
使われ方：table の行の開始位置から BE の逆像候補の頂点列を構成する。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：全射語の各位置で復元される行には全ての値が現れる（BF §1.4.2）。
方針：元の語の全射性と復元行の所属条件を合成する。
規約：位置は自然数で、終端以後も扱う。
使われ方：行の位置と値を同値にする。 -/
lemma mem_canonicalRow_word {n l : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word n l) (p : ℕ) (a : Fin n) :
    a ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow (List.ofFn v.val) p := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.mem_canonicalRow, List.mem_ofFn]
  exact v.surjective a

/-- 概要：復元行の添字と値の同値（BF §1.4.2）。
方針：重複のないリストの評価は単射で、全射語では全射でもある。
規約：この時点では行の長さと n の等式での移送を含めない。
使われ方：行の長さを arity と同定して置換を作る。 -/
def canonicalRowEquiv {n l : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word n l) (p : ℕ) :
    Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow (List.ofFn v.val) p).length ≃ Fin n :=
  Equiv.ofBijective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow (List.ofFn v.val) p).get
    ⟨List.nodup_iff_injective_get.mp (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow_nodup _ _),
      fun a => List.mem_iff_get.mp (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.mem_canonicalRow_word v p a)⟩

/-- 概要：全射語から復元した行の長さは arity（BF §1.4.2）。
方針：行の評価の同値の有限濃度を比較する。
規約：零 arity の空語も含む。
使われ方：復元行を Fin n の置換として扱う。 -/
lemma canonicalRow_word_length {n l : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word n l) (p : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow (List.ofFn v.val) p).length = n := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRowEquiv v p)

/-- 概要：全射語の指定位置で復元する BE の頂点置換（BF §1.4.2）。
方針：行の位置から値への同値を Fin n へ移して逆にする。
規約：table reduction はこの置換の逆を値の列として読む。
使われ方：区切りに対応する BE 置換列の頂点となる。 -/
def canonicalPermutation {n l : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word n l) (p : ℕ) : Equiv.Perm (Fin n) :=
  ((finCongr (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow_word_length v p).symm).trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRowEquiv v p)).symm

/-- 概要：復元頂点の逆置換の一行表示は指定した復元行（BF §1.4.2）。
方針：同値の合成を評価し、位置の自然数値が変わらないことを使う。
規約：BE の逆置換による table の規約と厳密に一致する。
使われ方：復元した置換列の table の各行を計算する。 -/
@[simp] lemma canonicalPermutation_inv_apply {n l : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word n l) (p : ℕ)
    (i : Fin n) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalPermutation v p)⁻¹ i =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow (List.ofFn v.val) p)[i.val]'(by
        rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow_word_length]; exact i.isLt) := rfl

/-- 概要：復元頂点を table の行へ戻すと復元行そのもの（BF §1.4.2）。
方針：全添字での逆置換の値を使ってリストを比較する。
規約：長さは arity で指定される。
使われ方：TR の各行の抽出をリストだけの計算へ帰着する。 -/
lemma canonicalPermutation_inv_list {n l : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word n l) (p : ℕ) :
    List.ofFn (fun i => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalPermutation v p)⁻¹ i) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow (List.ofFn v.val) p := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow_word_length]
  · intro i hi hj
    simp only [List.getElem_ofFn, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalPermutation_inv_apply]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
