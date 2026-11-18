module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.SubstitutionSingleton
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.SingletonHorizontalState
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.HorizontalRows
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SingletonRows
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix

/-!
模型。文献の定義との比較は後で
# 内側一文字の最終水平ブロックの実際の抽出

概要：Berger–Fresse §1.5.7 の最後の指定値を跨ぐ外側成分を実際の合成行列へ移す。
方針：内側可用行が一文字なら全行が水平ラベル像となることを各段で使う。
規約：指定値の最終除外前後の両方を同じ合成状態で扱う。
使われ方：外側最後の成分を任意の後続抽出へ接続する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：内側可用行が一文字の水平行の実際の合成抽出成功（BF §1.5.7）。
方針：全可用行と末尾以外の除外を水平ラベル像へ移し、終状態で後続に接続する。
規約：指定値が選択行の内部にあり最終除外される場合も含む。
使われ方：最終水平成分の一段の成功規則。 -/
lemma singletonHorizontalStep_success {m n : ℕ}
    (σ : Equiv.Perm (Fin (m + 1))) (τ : Equiv.Perm (Fin n)) (k : Fin (m + 1))
    (outer : List (Fin (m + 1))) (inner : List (Fin n)) (b : Fin n)
    (hinner : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available inner (List.ofFn τ.symm) = [b]) (r : ℕ) (hr : 0 < r)
    (hb : r ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available outer (List.ofFn σ.symm)).length)
    (rest : List (List (Fin (m + n)) × ℕ)) (tail : List (Fin (m + n)))
    (ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rest (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k
      (outer ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available outer (List.ofFn σ.symm)).take (r - 1)) inner) = some tail) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows ((List.ofFn (permutationComposition m n k σ τ).symm, r) :: rest)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner) =
      some (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available outer (List.ofFn σ.symm)).take r).map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel k b) ++ tail) := by
  let row := List.ofFn (permutationComposition m n k σ τ).symm
  have hrow := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.singleton_composite_available σ τ k outer inner b hinner
  have hlen : r ≤ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner) row).length := by
    rw [hrow, List.length_map]
    exact hb
  have hup : ∀ x, x ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner ++
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner) row).take (r - 1) ↔
      x ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k
        (outer ++ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available outer (List.ofFn σ.symm)).take (r - 1)) inner := by
    intro x
    rw [hrow, ← List.map_take]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel_singleton_state_update k b outer inner _
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.singleton_inner_cover τ inner b hinner) x
  have ht' := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_congr_removed rest _ _ hup).trans ht
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_cons_of_success row r rest _ tail hr hlen ht'
  simpa only [row, hrow, ← List.map_take] using hs

/-- 概要：内側可用行一文字のとき元の外側証跡全体を実際の合成表へ移す（BF §1.5.7）。
方針：指定値の最終除外を許す一段の成功規則を元の証跡に沿って反復する。
規約：終状態に指定値が残るという条件を要求しない。
使われ方：最後の外側成分を実際の合成行列で構成する。 -/
lemma singletonHorizontalExtraction_success {m n : ℕ}
    (τ : Equiv.Perm (Fin n)) (k : Fin (m + 1)) (inner : List (Fin n)) (b : Fin n)
    (hinner : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available inner (List.ofFn τ.symm) = [b])
    (vs : List (Equiv.Perm (Fin (m + 1)) × ℕ))
    (outer finish : List (Fin (m + 1))) (picked : List (List (Fin (m + 1))))
    (houter : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationRows vs) outer picked finish)
    (rest : List (List (Fin (m + n)) × ℕ)) (tail : List (Fin (m + n)))
    (ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rest (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k finish inner) = some tail) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedInnerRows τ k vs ++ rest) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner) =
      some (picked.flatten.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel k b) ++ tail) := by
  induction vs generalizing outer picked with
  | nil =>
    cases houter
    simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedInnerRows, List.map_nil, List.nil_append, List.flatten_nil] using ht
  | cons v vs ih =>
    obtain ⟨σ, r⟩ := v
    cases houter with
    | @cons _ _ _ _ remaining _ hr hb hnext =>
      have htail := ih _ _ hnext
      have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.singletonHorizontalStep_success σ τ k outer inner b hinner r hr hb
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedInnerRows τ k vs ++ rest)
        (remaining.flatten.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel k b) ++ tail) htail
      simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedInnerRows, List.map_cons, List.cons_append, List.flatten_cons,
        List.map_append, List.append_assoc] using hs

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
