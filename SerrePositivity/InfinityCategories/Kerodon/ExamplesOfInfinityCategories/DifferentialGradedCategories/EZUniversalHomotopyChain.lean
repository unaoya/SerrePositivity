module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.EZUniversalBoundary
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ExtraDegeneracyContraction

/-!
# 標準比較の普遍ホモトピー鎖の再帰的構成

概要：恒等と AW→shuffle の差を埋める一段上の普遍鎖を全次数で構成する。
方針：低次の交代面移送を差し引いたサイクルを先頭頂点の extra degeneracy で埋める。
規約：KST Construction A.5、比較の存在を追加の仮定にしない。
使われ方：任意の二つの入力へ評価して標準比較の実鎖ホモトピーを得る。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory Opposite AlgebraicTopology
open scoped Simplicial

/-- 概要：普遍模型内の正次数サイクルを先頭頂点の付加で充填する。
方針：自由化した実 extra degeneracy の鎖収縮等式を使う。
規約：KST A.5。使われ方：標準比較の各次数の再帰。 -/
lemma simplexPair_fill_cycle (N n : ℕ)
    (x : (linearizedSpace (simplexPairModel.{u} N)).obj (op ⦋n + 1⦌))
    (hx : ((alternatingFaceMapComplex _).obj (linearizedSpace (simplexPairModel N))).d
      (n + 1) n x = 0) :
    ((alternatingFaceMapComplex _).obj (linearizedSpace (simplexPairModel N))).d
      (n + 2) (n + 1) ((simplexPairLinearExtraDegeneracy N).s (n + 1) x) = x := by
  rw [alternatingFaceMapComplex_obj_d] at hx ⊢
  exact extraDegeneracy_fill_cycle (simplexPairLinearExtraDegeneracy N) n x hx

/-- 概要：標準比較の一段上の普遍ホモトピー鎖。
方針：零次は零とし、次の次数では差から低次の面移送を引いて extra degeneracy を適用する。
規約：KST Construction A.5、各次数は有限な整数鎖。
使われ方：標準比較ホモトピーの実成分を作用素評価で定義する。 -/
def ezUniversalHomotopyChain : (N : ℕ) →
    (linearizedSpace (simplexPairModel.{u} N)).obj (op ⦋N + 1⦌)
  | 0 => 0
  | n + 1 => (simplexPairLinearExtraDegeneracy (n + 1)).s (n + 1)
      (ezUniversalDifference (n + 1) - simplexPairFaceSum (op ⦋n + 1⦌) (ezUniversalHomotopyChain n))

/-- 概要：普遍ホモトピー鎖の零次の境界は普遍な差に一致。
方針：ホモトピーの零次と普遍な差の零次はともに零。
規約：KST A.5、非被約零次を含む。
使われ方：正次数でのサイクル性の帰納法の基底。 -/
lemma ezUniversalHomotopyChain_boundary_zero :
    ((alternatingFaceMapComplex _).obj (linearizedSpace (simplexPairModel.{u} 0))).d
      1 0 (ezUniversalHomotopyChain 0) = ezUniversalDifference 0 := by
  rw [ezUniversalHomotopyChain, map_zero, ezUniversalDifference_zero]

/-- 概要：普遍ホモトピー鎖の境界は差から低次の交代面移送を引いたもの。
方針：二重面移送の消滅と微分可換性により充填入力がサイクルであることを帰納的に示す。
規約：KST Construction A.5、標準比較の全次数での実充填。
使われ方：任意の単体的整数加群に評価した鎖ホモトピー等式。 -/
lemma ezUniversalHomotopyChain_boundary_succ (n : ℕ) :
    ((alternatingFaceMapComplex _).obj (linearizedSpace (simplexPairModel.{u} (n + 1)))).d
      (n + 2) (n + 1) (ezUniversalHomotopyChain (n + 1)) =
    ezUniversalDifference (n + 1) -
      simplexPairFaceSum (op ⦋n + 1⦌) (ezUniversalHomotopyChain n) := by
  induction n with
  | zero =>
    rw [ezUniversalHomotopyChain]
    apply simplexPair_fill_cycle 1 0
    rw [map_sub, ezUniversalDifference_boundary, simplexPairFaceSum_boundary,
      ezUniversalHomotopyChain_boundary_zero, sub_self]
  | succ n ih =>
    rw [ezUniversalHomotopyChain]
    apply simplexPair_fill_cycle (n + 1 + 1) (n + 1)
    rw [map_sub, ezUniversalDifference_boundary, simplexPairFaceSum_boundary, ih,
      simplexPairFaceSum_sub, simplexPairFaceSum_faceSum, sub_zero, sub_self]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
