module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.VerticalRows
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.CompositionExtractionStep
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.PermutationStateSubstitution
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix

/-!
模型。文献の定義との比較は後で
# 元の内側抽出証跡の固定外側合成表への転送

概要：Berger–Fresse §1.5.7 の垂直成分を実際の合成行列で抽出する。
方針：指定値が先頭の外側行を固定し、元の内側証跡の各行へ実際の一段の成功規則を適用する。
規約：後続の合成抽出は任意であり、終状態の所属の同値は既存の一段の規則で処理する。
使われ方：内側成分の語を合成表の垂直ブロックとして実際に抽出する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

open _root_.SerrePositivity.EInfinity.BarrattEccles _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：元の内側証跡を固定した外側頂点の合成行列へ転送（BF §1.5.7）。
方針：内側の各選択行で指定値への一出現代入の成功規則を使い、後続へ帰納する。
規約：元の証跡と任意の終状態からの後続成功だけを入力とする。
使われ方：合成経路の一つの垂直成分を後続の合成抽出へつなぐ。 -/
lemma verticalExtraction_success {m n : ℕ} (σ : Equiv.Perm (Fin (m + 1))) (k : Fin (m + 1))
    (outer : List (Fin (m + 1))) (post : List {a : Fin (m + 1) // a ≠ k})
    (houter : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available outer (List.ofFn σ.symm) = k :: post.map Subtype.val)
    (vs : List (Equiv.Perm (Fin n) × ℕ))
    (inner finish : List (Fin n)) (picked : List (List (Fin n)))
    (hinner : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ExtractionPrefix (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationRows vs) inner picked finish)
    (rest : List (List (Fin (m + n)) × ℕ)) (tail : List (Fin (m + n)))
    (ht : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows rest (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer finish) = some tail) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedOuterRows σ k vs ++ rest) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionStateRemoved k outer inner) =
      some (picked.flatten.map (insertedPosition m n k) ++ tail) := by
  induction vs generalizing inner picked with
  | nil =>
    cases hinner
    simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedOuterRows, List.map_nil, List.nil_append, List.flatten_nil] using ht
  | cons v vs ih =>
    obtain ⟨τ, r⟩ := v
    cases hinner with
    | @cons _ _ _ _ remaining _ hr hb hnext =>
      have hrow := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationComposition_state_available_substitute σ τ k outer inner
      rw [houter] at hrow
      have htail := ih _ _ hnext
      have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.compositionExtractionStep_inside k outer inner
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.available inner (List.ofFn τ.symm)) [] post
        (List.ofFn (permutationComposition m n k σ τ).symm) r
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedOuterRows σ k vs ++ rest)
        (remaining.flatten.map (insertedPosition m n k) ++ tail) hrow hr hb (by
          simpa only [List.map_nil, List.append_nil] using htail)
      simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.fixedOuterRows, List.map_cons, List.cons_append, List.length_nil,
        Nat.zero_add, List.map_nil, List.nil_append, List.flatten_cons, List.map_append,
        List.append_assoc] using hs

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
