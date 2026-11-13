module

public import SerrePositivity.EInfinity.SimplexCuts.RawAction

/-!
# 一般の BF 切断微分の項の添字

Berger–Fresse §2.2.6–7、M14 L09a。
出力の面、係数語の文字削除、入力の面を、零となる場合も残した有限型で保持する。
この型だけで微分の等式や項の対応の存在を仮定しない。
-/

@[expose] public section
namespace SerrePositivity.EInfinity.SimplexCuts

/-- テンソル出力の一つの色の面を削除する項。
次数零の色の唯一の添字は、境界の値の定義で零にする。 -/
abbrev OutputBoundaryIndex {r d : ℕ} (u : Surjection.BasisWord (r + 1) d) (q : ℕ) :=
  Σ s : Cut (r + d) q, Σ a : Fin (r + 1), Fin (outputDegree s (positiveWord u) a + 1)

/-- 係数語の一文字を削除した後の切断の添字。
d=0、非全射、隣接値が同じになる削除は、値の定義で零にする。 -/
abbrev CoefficientBoundaryIndex (r d q : ℕ) :=
  Fin (r + d + 1) × Cut (r + d - 1) q

/-- 入力単体の面を削除した後の切断の添字。q=0 の値は零にする。 -/
abbrev SimplexBoundaryIndex (r d q : ℕ) := Fin (q + 1) × Cut (r + d) (q - 1)

/-- L09a の符号付き境界項の全添字。右辺に由来する二群の負号は値側に保持する。 -/
abbrev BoundaryBalanceIndex {r d : ℕ} (u : Surjection.BasisWord (r + 1) d) (q : ℕ) :=
  OutputBoundaryIndex u q ⊕ (CoefficientBoundaryIndex r d q ⊕ SimplexBoundaryIndex r d q)

end SerrePositivity.EInfinity.SimplexCuts
