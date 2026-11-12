module
public import SerrePositivity.KST.ProExcision.IntegerIntervalComparison

/-!
# 単体的区間の定数単体に対する鎖比較

概要：端点の定数単体は零次で対応する頂点へ移り、正次数で零になる。
方針：頂点の値の差が零であることと高次の零成分を使う。
規約：KST Definition A.3、Construction A.5、非被約な零次を保持。
使われ方：AW で区間次数0の切断だけを残し、復元の両端を検証する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：区間の端点の定数単体の頂点の値は指定端点。
方針：標準単体の定数写像を評価する。
規約：KST A.3。使われ方：定数単体の辺の重みの零性。 -/
lemma intervalSimplexVertex_constant (n : ℕ) (i : Fin 2) (j : Fin (n + 1)) :
    intervalSimplexVertex (SSet.stdSimplex.const 1 i (op ⦋n⦌) :
      (Δ[1] : SSet.{u}).obj (op ⦋n⦌)) j = i := rfl

/-- 概要：区間の定数単体は単体射による制限で同じ定数単体に移る。
方針：二つの単体圏の射を頂点上で比較する。
規約：KST A.3。使われ方：AW の後半制限に沿う端点の評価。 -/
lemma intervalConstant_map {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) (i : Fin 2) :
    (Δ[1] : SSet.{u}).map f.op (SSet.stdSimplex.const 1 i (op ⦋m⦌)) =
      SSet.stdSimplex.const 1 i (op ⦋n⦌) := by
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  ext j
  rfl

/-- 概要：零次の定数単体は対応する区間の頂点へ移る。
方針：区間比較の零次の基底評価を使う。
規約：KST A.3。使われ方：復元した区間射の両端の値。 -/
lemma integerIntervalComparison_constant_zero (i : Fin 2) :
    integerIntervalComparison.f 0
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (SSet.stdSimplex.const 1 i (op ⦋0⦌) :
        (Δ[1] : SSet.{u}).obj (op ⦋0⦌))) = integerIntervalVertex i :=
  integerIntervalComparisonApp_zero_generator _

/-- 概要：正次数の定数単体は区間の鎖比較で零へ移る。
方針：一次では両端の値の差が零、二次以降では比較成分が零。
規約：KST A.3・A.5。使われ方：AW の区間の正次数の項の消去。 -/
lemma integerIntervalComparison_constant_succ (n : ℕ) (i : Fin 2) :
    integerIntervalComparison.f (n + 1)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (SSet.stdSimplex.const 1 i (op ⦋n + 1⦌) :
        (Δ[1] : SSet.{u}).obj (op ⦋n + 1⦌))) = 0 := by
  cases n with
  | zero =>
    change integerIntervalComparisonApp 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator _) = _
    rw [integerIntervalComparisonApp_one_generator]
    simp only [intervalSimplexVertex_constant, integerIntervalWeight, sub_self, zero_smul]
  | succ n => rfl

/-- 概要：区間の任意の正次数の定数単体は零へ移る。
方針：次数が零の場合を除き、一つ高い次数の公式へ帰着する。
規約：KST A.3・A.5。使われ方：AW の N−i 次数の項の消去。 -/
lemma integerIntervalComparison_constant_of_pos (n : ℕ) (hn : 0 < n) (i : Fin 2) :
    integerIntervalComparison.f n
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (SSet.stdSimplex.const 1 i (op ⦋n⦌) :
        (Δ[1] : SSet.{u}).obj (op ⦋n⦌))) = 0 := by
  cases n with
  | zero => omega
  | succ n => exact integerIntervalComparison_constant_succ n i

end SerrePositivity.KST.ProExcision
