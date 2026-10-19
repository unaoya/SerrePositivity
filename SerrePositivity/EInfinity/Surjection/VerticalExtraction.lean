module

public import SerrePositivity.EInfinity.Surjection.VerticalRows
public import SerrePositivity.EInfinity.Surjection.CompositionExtractionStep
public import SerrePositivity.EInfinity.Surjection.PermutationStateSubstitution
public import SerrePositivity.EInfinity.TableReduction.ExtractionPrefix

/-!
# 元の内側抽出証跡の固定外側合成表への転送

概要：Berger–Fresse §1.5.7 の垂直成分を実際の合成行列で抽出する。
方針：指定値が先頭の外側行を固定し、元の内側証跡の各行へ実際の一段の成功規則を適用する。
規約：後続の合成抽出は任意であり、終状態の所属の同値は既存の一段の規則で処理する。
使われ方：内側成分の語を合成表の垂直ブロックとして実際に抽出する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.Surjection

open BarrattEccles TableReduction

/-- 概要：元の内側証跡を固定した外側頂点の合成行列へ転送（BF §1.5.7）。
方針：内側の各選択行で指定値への一出現代入の成功規則を使い、後続へ帰納する。
規約：元の証跡と任意の終状態からの後続成功だけを入力とする。
使われ方：合成経路の一つの垂直成分を後続の合成抽出へつなぐ。 -/
lemma verticalExtraction_success {m n : ℕ} (σ : Equiv.Perm (Fin (m + 1))) (k : Fin (m + 1))
    (outer : List (Fin (m + 1))) (post : List {a : Fin (m + 1) // a ≠ k})
    (houter : available outer (List.ofFn σ.symm) = k :: post.map Subtype.val)
    (vs : List (Equiv.Perm (Fin n) × ℕ))
    (inner finish : List (Fin n)) (picked : List (List (Fin n)))
    (hinner : ExtractionPrefix (permutationRows vs) inner picked finish)
    (rest : List (List (Fin (m + n)) × ℕ)) (tail : List (Fin (m + n)))
    (ht : reduceRows rest (compositionStateRemoved k outer finish) = some tail) :
    reduceRows (fixedOuterRows σ k vs ++ rest) (compositionStateRemoved k outer inner) =
      some (picked.flatten.map (insertedPosition m n k) ++ tail) := by
  induction vs generalizing inner picked with
  | nil =>
    cases hinner
    simpa only [fixedOuterRows, List.map_nil, List.nil_append, List.flatten_nil] using ht
  | cons v vs ih =>
    obtain ⟨τ, r⟩ := v
    cases hinner with
    | @cons _ _ _ _ remaining _ hr hb hnext =>
      have hrow := permutationComposition_state_available_substitute σ τ k outer inner
      rw [houter] at hrow
      have htail := ih _ _ hnext
      have hs := compositionExtractionStep_inside k outer inner
        (available inner (List.ofFn τ.symm)) [] post
        (List.ofFn (permutationComposition m n k σ τ).symm) r
        (fixedOuterRows σ k vs ++ rest)
        (remaining.flatten.map (insertedPosition m n k) ++ tail) hrow hr hb (by
          simpa only [List.map_nil, List.append_nil] using htail)
      simpa only [fixedOuterRows, List.map_cons, List.cons_append, List.length_nil,
        Nat.zero_add, List.map_nil, List.nil_append, List.flatten_cons, List.map_append,
        List.append_assoc] using hs

end SerrePositivity.EInfinity.Surjection
