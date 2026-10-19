module

public import SerrePositivity.EInfinity.TableReduction.ReductionRows

/-!
# 語の位置から決まる行内添字

概要：Berger–Fresse §1.5.7 の成分端点を実際の抽出行の内部位置へ移す。
方針：所属行の開始位置を元の出力位置から引き、行内上界を所属区間から得る。
規約：末尾位置もその行の最後の有限添字として扱う。
使われ方：成分端点の文字と、その前後の利用可能行を同じ位置で評価する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.TableReduction

/-- 概要：成功表の指定出力位置の所属行内の有限添字（BF §1.5.7）。
方針：元の位置から所属行の開始位置を引く。
規約：行添字は既存の reductionRow で固定する。
使われ方：合成行で指定文字の前後の部分を取り出す。 -/
def reductionColumn {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : Schedule n d)
    (v : Fin (n + d) → Fin n) (h : reduceRows (rows w r) [] = some (List.ofFn v))
    (p : Fin (n + d)) : Fin (r.val (reductionRow w r v h p)).val :=
  ⟨p.val - scheduleOffset r (reductionRow w r v h p), by
    have hb := reductionRow_bounds w r v h p
    omega⟩

/-- 概要：行開始位置と行内添字の和は元の出力位置（BF §1.5.7）。
方針：元の位置が所属行開始以降であることを使い、自然数の差を戻す。
規約：最終行末を含む。
使われ方：元の出力語と利用可能な逆置換行を同じ添字で比較する。 -/
lemma reductionColumn_position {n d : ℕ}
    (w : Fin (d + 1) → Equiv.Perm (Fin n)) (r : Schedule n d)
    (v : Fin (n + d) → Fin n) (h : reduceRows (rows w r) [] = some (List.ofFn v))
    (p : Fin (n + d)) :
    p.val = scheduleOffset r (reductionRow w r v h p) + (reductionColumn w r v h p).val := by
  have hb := (reductionRow_bounds w r v h p).1
  change p.val = scheduleOffset r (reductionRow w r v h p) +
    (p.val - scheduleOffset r (reductionRow w r v h p))
  omega

end SerrePositivity.EInfinity.TableReduction
