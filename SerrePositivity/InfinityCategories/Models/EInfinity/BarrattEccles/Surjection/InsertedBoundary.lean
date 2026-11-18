module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.HorizontalBoundary
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.VerticalBoundary

/-!
模型。文献の定義との比較は後で
# 選択行の境界の内側二文字による辺方向の判定

概要：Berger–Fresse §1.5.8 の逆構成で、垂直辺と水平辺を実際の選択語の両端から区別する。
方針：垂直辺の両端は挿入ラベルで、水平辺の両端が挿入ラベルなら同じ値となり退化する。
規約：任意の除外状態・後続表・内外の置換に適用する。
使われ方：同じ非退化出力を持つ shuffle 経路の一意性を証明する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：隣接選択語の末尾と先頭がともに挿入ラベルとなる条件（BF §1.5.8）。
方針：実際の末尾・先頭とその内側射影値を存在証明として保持する。
規約：語が空なら条件は満たされない。
使われ方：出力語だけで定まる境界から垂直辺を検出する。 -/
def InsertedJoin {m n : ℕ} (k : Fin (m + 1)) (left right : List (Fin (m + n))) : Prop :=
  (∃ a c, left.getLast? = some a ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k a = some c) ∧
    (∃ b d, right.head? = some b ∧ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel k b = some d)

/-- 概要：非退化な成功垂直二行の選択境界は両方が内側（BF §1.5.8）。
方針：正の行長で実際の境界二文字を取り出し、垂直端点の一般補題を使う。
規約：前後の選択は元の成功による take そのもの。
使われ方：経路の垂直辺を選択行列の境界へ符号化する。 -/
lemma vertical_inserted_join {m n : ℕ} (k : Fin (m + 1))
    (σ : Equiv.Perm (Fin (m + 1))) (τ τ' : Equiv.Perm (Fin n))
    (r s : ℕ) (rest : List (List (Fin (m + n)) × ℕ)) (removed out : List (Fin (m + n)))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows
      ((List.ofFn (permutationComposition m n k σ τ).symm, r) ::
        (List.ofFn (permutationComposition m n k σ τ').symm, s) :: rest) removed = some out)
    (hc : out.IsChain (· ≠ ·)) :
    let xs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (List.ofFn (permutationComposition m n k σ τ).symm)
    let ys := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ xs.take (r - 1))
      (List.ofFn (permutationComposition m n k σ τ').symm)
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.InsertedJoin k (xs.take r) (ys.take s) := by
  obtain ⟨hr, hb, tail, ht, _⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ h
  obtain ⟨hs, hsb, _, _, _⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ ht
  let xs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (List.ofFn (permutationComposition m n k σ τ).symm)
  let rem := removed ++ xs.take (r - 1)
  let ys := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available rem (List.ofFn (permutationComposition m n k σ τ').symm)
  have hi : r - 1 < xs.length := by change r ≤ xs.length at hb; omega
  have hj : 0 < ys.length := by change s ≤ ys.length at hsb; omega
  let a := xs[r - 1]
  let b := ys[0]
  have he : xs[r - 1]? = some a := List.getElem?_eq_getElem hi
  have hh : ys.head? = some b := by
    rw [List.head?_eq_getElem?]
    exact List.getElem?_eq_getElem hj
  obtain ⟨c, ha⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_vertical_endpoint_inserted σ τ τ' k removed out
    a r s rest he h hc
  obtain ⟨d, hb'⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_vertical_next_head_inserted σ τ τ' k removed out
    a b r s rest he hh h hc
  refine ⟨⟨a, c, ?_, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_eq_some_iff k a c).mpr ha⟩,
    ⟨b, d, ?_, (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.innerLabel_eq_some_iff k b d).mpr hb'⟩⟩
  · rw [List.getLast?_take, ite_eq_right (show r ≠ 0 by omega), he, Option.some_or]
  · rw [List.head?_take, ite_eq_right (show s ≠ 0 by omega)]
    exact hh

/-- 概要：非退化な成功水平二行の選択境界は両方内側にはならない（BF §1.5.8）。
方針：両端が内側なら同じ内側置換の共有端点で一致し、元の境界の非退化性に矛盾する。
規約：元の行長条件は成功から導く。
使われ方：選択行列から水平辺と垂直辺を区別する。 -/
lemma horizontal_not_inserted_join {m n : ℕ} (k : Fin (m + 1))
    (σ σ' : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin n))
    (r s : ℕ) (rest : List (List (Fin (m + n)) × ℕ)) (removed out : List (Fin (m + n)))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows
      ((List.ofFn (permutationComposition m n k σ τ).symm, r) ::
        (List.ofFn (permutationComposition m n k σ' τ).symm, s) :: rest) removed = some out)
    (hc : out.IsChain (· ≠ ·)) :
    let xs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (List.ofFn (permutationComposition m n k σ τ).symm)
    let ys := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (removed ++ xs.take (r - 1))
      (List.ofFn (permutationComposition m n k σ' τ).symm)
    ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.InsertedJoin k (xs.take r) (ys.take s) := by
  obtain ⟨hr, hb, tail, ht, _⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ h
  obtain ⟨hs, _, _, _, _⟩ := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_success _ _ _ _ _ ht
  let xs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available removed (List.ofFn (permutationComposition m n k σ τ).symm)
  let rem := removed ++ xs.take (r - 1)
  let ys := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available rem (List.ofFn (permutationComposition m n k σ' τ).symm)
  change ¬ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery.InsertedJoin k (xs.take r) (ys.take s)
  rintro ⟨⟨a, c, he, ha⟩, ⟨b, d, hh, hb'⟩⟩
  have hi : r - 1 < xs.length := by change r ≤ xs.length at hb; omega
  have he' : xs[r - 1]? = some a := by
    rw [List.getLast?_take, ite_eq_right (show r ≠ 0 by omega),
      List.getElem?_eq_getElem hi, Option.some_or] at he
    exact (List.getElem?_eq_getElem hi).trans he
  have hh' : ys.head? = some b := by
    rw [List.head?_take, ite_eq_right (show s ≠ 0 by omega)] at hh
    exact hh
  have hne := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_boundary_ne _ _ r s rest removed out a b he' hh' h hc
  exact hne (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_horizontal_inner_boundary_eq σ σ' τ k removed r hr
    a b c d he' hh' ha hb')

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositeRecovery
