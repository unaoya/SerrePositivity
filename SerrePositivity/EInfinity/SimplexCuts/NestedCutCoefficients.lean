module

public import SerrePositivity.EInfinity.SimplexCuts.CompositeFaceFamilies

/-!
# 元の二段切断の二つの係数移動と切断符号

Berger–Fresse §2.2.4–6・§3.1、M14 L12a。
元の前方出力次数、係数交換d*e、元の内外cutSignを保持する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- 元の指定出力より前の実テンソルの総次数（BF §3.1）。 -/
def positiveNestedPrefixDegree {m d q : ℕ} (u : Surjection.BasisWord (m + 1) d)
    (k : Fin (m + 1)) (s : Cut (m + d) q) : ℕ :=
  degreeSum k.val (IntervalCuts.prefixFamily (outputDegree s (positiveWord u)) k)

/-- 元の二つの係数移動と内外の切断の整数符号の積（BF §2.2.6・§3.1）。 -/
def positiveNestedCutCoefficient {m n d e q : ℕ}
    (u : Surjection.BasisWord (m + 1) d) (v : Surjection.BasisWord (n + 1) e)
    (k : Fin (m + 1)) (c : PositiveNestedCutIndex u v k q) : ℤ :=
  (-1 : ℤ) ^ (d * e + e * positiveNestedPrefixDegree u k c.1) *
    cutSign c.1 (positiveWord u).val * cutSign c.2 (positiveWord v).val

end SerrePositivity.EInfinity.SimplexCuts
