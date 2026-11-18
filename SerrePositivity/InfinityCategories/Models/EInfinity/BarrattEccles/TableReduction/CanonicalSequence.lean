module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CanonicalPermutations
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.TableStarts
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Sequence
public import SerrePositivity.EInfinity.BarrattEccles.Simplicial

/-!
模型。文献の定義との比較は後で
# 全射語からの標準置換列の復元

概要：Berger–Fresse §1.4.2 の全射性の逆像候補の置換列を構成する。
方針：語の各 table 行の開始位置で復元した置換を頂点として並べる。
規約：ここでは候補単体を構成し、TR が元の語になることは後続の工程で証明する。
使われ方：一般の TR の全射性の明示的な逆像の入力となる。
-/

@[expose] public section

noncomputable section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
open scoped _root_.Simplicial

/-- 概要：全射語の各区切りに対応する標準頂点列（BF §1.4.2）。
方針：d+1 個の開始位置で各値の順序から置換を復元する。
規約：BE の頂点は位置の作用なので値の行表示を逆にする。
使われ方：TR の全射性の逆像候補の頂点を供給する。 -/
def canonicalVertices {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) :
    Fin (d + 1) → Equiv.Perm (Fin n) :=
  fun i => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalPermutation v (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i)

/-- 概要：全射語から復元した BE 単体の候補（BF §1.4.2）。
方針：標準頂点列を既存の単体と置換列の同値で戻す。
規約：非退化性と TR の値の同定はまだ主張しない。
使われ方：TR の全射性の証明で実際の EΣ_n の単体を指定する。 -/
def canonicalSimplex {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) :
    (_root_.SerrePositivity.EInfinity.BarrattEccles.simplicial n) _⦋d⦌ :=
  (_root_.SerrePositivity.EInfinity.BarrattEccles.simplexEquiv n d).symm (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalVertices v)

/-- 概要：復元単体の頂点列は指定した標準頂点列（BF §1.4.2）。
方針：単体と置換列の同値の右逆を使う。
規約：全ての頂点で厳密に一致する。
使われ方：実際の単体に適用した TR をリストの計算に移す。 -/
@[simp] lemma simplexEquiv_canonicalSimplex {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) :
    _root_.SerrePositivity.EInfinity.BarrattEccles.simplexEquiv n d (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalSimplex v) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalVertices v :=
  (_root_.SerrePositivity.EInfinity.BarrattEccles.simplexEquiv n d).apply_symm_apply _

/-- 概要：標準頂点列の table の行は復元した文字列（BF §1.4.2）。
方針：各頂点の逆置換のリスト表示を簡約する。
規約：行長は任意の Schedule を許す。
使われ方：指定外の行長で出力が退化することを検証する。 -/
lemma rows_canonicalVertices {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalVertices v) r =
      List.ofFn (fun i =>
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow (List.ofFn v.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i), (r.val i).val)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalVertices, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalPermutation_inv_list]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
