module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.HorizontalRows
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.HorizontalExtractionStep
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.PrefixStateMonotone

/-!
模型。文献の定義との比較は後で
# 最終除外前の外側証跡の実際の水平合成ブロックへの転送

概要：Berger–Fresse §1.5.7 の水平成分の全行を固定内側の実際の置換部分合成へ移す。
方針：終状態で指定値が残ることから各行の末尾以外の不出現を得て、行数で帰納する。
規約：内側の行と進行状態を固定し、その先頭文字を指定値の像とする。
使われ方：任意の後続成功に元の水平成分全体の成功を接続する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：最終除外前の元の外側証跡を実際の固定内側合成表へ移す（BF §1.5.7）。
方針：元の終状態の未除外性を各段へ戻し、一行の水平成功規則を反復する。
規約：内側の未選択文字は終始残し、指定値を選ぶ場合は先頭文字一つを使う。
使われ方：合成経路の水平成分を任意の後続抽出へつなぐ。 -/
lemma horizontalExtraction_success {m n : ℕ} (τ : Equiv.Perm (Fin n)) (k : Fin (m + 1))
    (inner : List (Fin n)) (b : Fin n) (ys : List (Fin n))
    (hinner : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available inner (List.ofFn τ.symm) = b :: ys)
    (vs : List (Equiv.Perm (Fin (m + 1)) × ℕ))
    (outer finish : List (Fin (m + 1))) (picked : List (List (Fin (m + 1))))
    (houter : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationRows vs) outer picked finish) (hk : k ∉ finish)
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
      have hn := hnext.not_mem_initial k hk
      have hprefix : k ∉ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available outer (List.ofFn σ.symm)).take (r - 1) := by
        intro hm
        exact hn (List.mem_append_right _ hm)
      have htail := ih _ _ hnext
      have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalExtractionStep_success σ τ k outer inner b ys hinner r hr hb hprefix
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedInnerRows τ k vs ++ rest)
        (remaining.flatten.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.horizontalLabel k b) ++ tail) htail
      simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedInnerRows, List.map_cons, List.cons_append, List.flatten_cons,
        List.map_append, List.append_assoc] using hs

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
