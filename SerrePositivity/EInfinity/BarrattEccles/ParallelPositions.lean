module

public import SerrePositivity.EInfinity.BarrattEccles.ParallelPositionValues

/-!
# 異なる二入力への挿入の位置の同定

概要：Berger–Fresse §0.10 の並列の二段の挿入を有限入力集合上で比較する。
方針：残りの入力と各挿入区間を表す部分型を作り、数値の位置の等式を Fin の等式へ戻す。
規約：二つの指定位置は任意の異なる位置で、順序の仮定を置かない。
使われ方：置換の部分合成の並列結合則で三種類の入力を比較する。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.BarrattEccles

/-- 概要：最初に i へ代入した後に残る二つ目の指定位置 j（Berger–Fresse §0.10）。
方針：残りの入力の位置を二回目の部分合成の arity の表記へ移す。
規約：j は i と異なる。
使われ方：並列の二回目の部分合成の位置を指定する。 -/
def parallelSlot (m n : ℕ) (i j : Fin (m + 2)) (hji : j ≠ i) : Fin (m + n + 1) :=
  Fin.cast (by omega : m + 1 + n = m + n + 1) (remainingPosition (m + 1) n i ⟨j, hji⟩)

/-- 概要：二回目の指定位置の値は残りの入力の番号の公式に従う（Berger–Fresse §0.10）。
方針：Fin.cast が値を変えないことと残りの位置の値の公式を使う。
規約：指定位置の順序を仮定しない。
使われ方：並列の位置の同定を数値の公式へ帰着する。 -/
lemma parallelSlot_val (m n : ℕ) (i j : Fin (m + 2)) (hji : j ≠ i) :
    (parallelSlot m n i j hji).val = remainingValue n i.val j.val := by
  exact remainingPosition_val (m + 1) n i ⟨j, hji⟩

/-- 概要：元の二つの指定位置と異なる入力は一回目の後にも二回目の指定位置と異なる（Berger–Fresse §0.10）。
方針：残りの入力の番号の単射性を使う。
規約：a は i,j の両方と異なる。
使われ方：外側の残りの入力へ二回目の挿入を適用する。 -/
def parallelOuterRemaining (m n : ℕ) (i j : Fin (m + 2)) (hji : j ≠ i)
    (a : {a : Fin (m + 2) // a ≠ i ∧ a ≠ j}) :
    {b : Fin (m + n + 1) // b ≠ parallelSlot m n i j hji} :=
  ⟨Fin.cast (by omega : m + 1 + n = m + n + 1)
      (remainingPosition (m + 1) n i ⟨a.val, a.property.1⟩), by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_cast, parallelSlot_val, remainingPosition_val] at hv
    exact a.property.2 (Fin.ext (remainingValue_injective n i.val a.val.val j.val
      (fun h => a.property.1 (Fin.ext h)) (fun h => hji (Fin.ext h)) hv))⟩

/-- 概要：一回目に挿入した区間の入力は二回目の指定位置と異なる（Berger–Fresse §0.10）。
方針：残りの入力の番号が挿入区間の番号と異なることを使う。
規約：a は最初に挿入した n 入力の区間に属する。
使われ方：最初の挿入区間へ二回目の挿入による位置移動を適用する。 -/
def parallelInnerRemaining (m n : ℕ) (i j : Fin (m + 2)) (hji : j ≠ i) (a : Fin n) :
    {b : Fin (m + n + 1) // b ≠ parallelSlot m n i j hji} :=
  ⟨Fin.cast (by omega : m + 1 + n = m + n + 1) (insertedPosition (m + 1) n i a), by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_cast, parallelSlot_val, insertedPosition_val] at hv
    exact remainingValue_ne_inserted n i.val j.val a.val (fun h => hji (Fin.ext h)) a.isLt hv.symm⟩

/-- 概要：外側の残りの入力の位置は独立な二つの挿入の順序に依存しない（Berger–Fresse §0.10）。
方針：両辺の値を残りの入力の番号の二段の公式に直す。
規約：最終 arity m+n+k と m+k+n を等式で移送する。
使われ方：置換の並列結合則の外側の入力を比較する。 -/
lemma parallelPosition_outer (m n k : ℕ) (i j : Fin (m + 2)) (hji : j ≠ i)
    (a : {a : Fin (m + 2) // a ≠ i ∧ a ≠ j}) :
    Fin.cast (by omega : m + n + k = m + k + n)
        (remainingPosition (m + n) k (parallelSlot m n i j hji)
          (parallelOuterRemaining m n i j hji a)) =
      remainingPosition (m + k) n (parallelSlot m k j i hji.symm)
        (parallelOuterRemaining m k j i hji.symm ⟨a.val, a.property.2, a.property.1⟩) := by
  apply Fin.ext
  simp only [Fin.val_cast, remainingPosition_val, parallelSlot_val, parallelOuterRemaining]
  exact remainingValue_parallel n k i.val j.val a.val.val
    (fun h => hji (Fin.ext h.symm)) (fun h => a.property.1 (Fin.ext h))
    (fun h => a.property.2 (Fin.ext h))

/-- 概要：一方の挿入区間の入力の位置は二つの挿入順序で一致する（Berger–Fresse §0.10）。
方針：数値の挿入区間の移動の公式を Fin の等式へ戻す。
規約：左辺で最初に i へ挿入した区間は、右辺では後から同じ位置へ挿入される。
使われ方：置換の並列結合則の各挿入区間の入力を比較する。 -/
lemma parallelPosition_inside (m n k : ℕ) (i j : Fin (m + 2)) (hji : j ≠ i) (a : Fin n) :
    Fin.cast (by omega : m + n + k = m + k + n)
        (remainingPosition (m + n) k (parallelSlot m n i j hji)
          (parallelInnerRemaining m n i j hji a)) =
      insertedPosition (m + k) n (parallelSlot m k j i hji.symm) a := by
  apply Fin.ext
  simp only [Fin.val_cast, remainingPosition_val, parallelSlot_val, parallelInnerRemaining,
    insertedPosition_val]
  exact insertedValue_parallel n k i.val j.val a.val (fun h => hji (Fin.ext h.symm)) a.isLt

end SerrePositivity.EInfinity.BarrattEccles
