module

public import SerrePositivity.EInfinity.TableReduction.ReductionInterval
public import SerrePositivity.EInfinity.Surjection.PermutationRowLift

/-!
# 成分区間の元の置換頂点と行長

概要：Berger–Fresse §1.5.7 の区間証明書を元の置換頂点列と行長の列として公開する。
方針：証明済みの連続する元の行表示へ、その行長を zip する。
規約：元の置換列の区間をそのまま使い、新たな逆像置換は選ばない。
使われ方：内側成分を実際の置換部分合成の行列へ転送する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.TableReduction.ReductionInterval

open Surjection

/-- 概要：成分を抽出する元の置換頂点と選択長さの列（BF §1.5.7）。
方針：元の成功表の連続する頂点と成分証明書の行長を zip する。
規約：両端を含める。
使われ方：固定外側での実際の部分合成の行列を作る入力。 -/
def weightedVertices {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)}
    {r : Schedule n d} {v : Fin (n + d) → Fin n}
    {h : reduceRows (rows w r) [] = some (List.ofFn v)} {p q : Fin (n + d)}
    (c : ReductionInterval w r v h p q) : List (Equiv.Perm (Fin n) × ℕ) :=
  (((List.ofFn w).drop (Surjection.lineRank v p.val)).take
    (Surjection.lineRank v q.val - Surjection.lineRank v p.val + 1)).zip (c.part.map Prod.snd)

/-- 概要：元の置換頂点と行長を行表示に戻すと同じ成分行列（BF §1.5.7）。
方針：元の行表示の連続区間の一致と zip の復元公式を使う。
規約：選択長さも元の成分証明書と一致する。
使われ方：成分の先行証跡を置換頂点を持つ実際の行列へ移す。 -/
lemma permutationRows_eq {n d : ℕ} {w : Fin (d + 1) → Equiv.Perm (Fin n)}
    {r : Schedule n d} {v : Fin (n + d) → Fin n}
    {h : reduceRows (rows w r) [] = some (List.ofFn v)} {p q : Fin (n + d)}
    (c : ReductionInterval w r v h p q) : permutationRows c.weightedVertices = c.part := by
  apply permutationRows_zip
  rw [c.source]
  simp only [List.map_take, List.map_drop, List.map_ofFn, rows, Function.comp_def]
  rfl

end SerrePositivity.EInfinity.TableReduction.ReductionInterval
