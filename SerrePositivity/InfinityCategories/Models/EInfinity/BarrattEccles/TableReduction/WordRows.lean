module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CanonicalSequence

/-!
模型。文献の定義との比較は後で
# 標準行を任意の行長で並べた有限リスト

概要：Berger–Fresse §1.4.3 の全行の帰納法で使う table の後続リストを指定する。
方針：各開始位置の復元行と行長を ofFn で並べ、drop で後続を取る。
規約：行長は任意の自然数値の関数で、Schedule の条件をここでは課さない。
使われ方：正しい抽出と行長の一意性を同じリストの族で証明する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：標準復元行と指定した行長のリスト（BF §1.4.3）。
方針：有限な行添字でリスト化する。
規約：行長の妥当性は別に証明する。
使われ方：標準 table の全行の抽出の入力。 -/
def wordRows {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (r : Fin (d + 1) → ℕ) :
    List (List (Fin n) × ℕ) :=
  List.ofFn (fun i => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow (List.ofFn v.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i), r i))

/-- 概要：標準 table の行数は d+1（BF §1.4.3）。
方針：ofFn の長さを読む。
規約：次数零も含む。
使われ方：後続行リストの添字と最後の行を扱う。 -/
@[simp] lemma wordRows_length {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (r : Fin (d + 1) → ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.wordRows v r).length = d + 1 := List.length_ofFn

/-- 概要：指定した行からの後続リストを先頭行と残りへ分割（BF §1.4.3）。
方針：drop の先頭を ofFn の評価で計算する。
規約：指定行は必ず範囲内。
使われ方：reduceRows の一段の再帰を適用する。 -/
lemma wordRows_drop_cons {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (r : Fin (d + 1) → ℕ)
    (i : Fin (d + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.wordRows v r).drop i.val =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow (List.ofFn v.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v i), r i) ::
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.wordRows v r).drop (i.val + 1) := by
  rw [List.drop_eq_getElem_cons (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.wordRows_length]; exact i.isLt)]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.wordRows, List.getElem_ofFn, Fin.eta]

/-- 概要：最後の行からの後続は一行だけ（BF §1.4.3）。
方針：先頭行を分けた後の drop は行数を超えて空になる。
規約：次数零でも同じ式。
使われ方：後方帰納法の基底を与える。 -/
lemma wordRows_drop_last {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (r : Fin (d + 1) → ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.wordRows v r).drop d =
      [(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalRow (List.ofFn v.val) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.rowStart v (Fin.last d)), r (Fin.last d))] := by
  have he := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.wordRows_drop_cons v r (Fin.last d)
  have hn : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.wordRows v r).drop (d + 1) = [] := by
    apply List.drop_eq_nil_iff.mpr
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.wordRows_length]
  simpa only [Fin.val_last, hn] using he

/-- 概要：置換から計算する標準 table は wordRows と一致（BF §1.4.3）。
方針：各頂点の逆置換の一行表示を復元行へ戻す。
規約：任意の Schedule で成立する。
使われ方：行のリストの証明を実際の TR の各項へ渡す。 -/
lemma rows_canonical_eq_wordRows {n d : ℕ} (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord n d) (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.canonicalVertices v) r = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.wordRows v (fun i => (r.val i).val) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows_canonicalVertices]
  rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
