module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.ProExcision.TensorAugmentationMHomotopy
public import SerrePositivity.KST.ProExcision.LinearizedGroupProduct

/-!
# Construction A.5 の明示的な非可換標的への特殊化

概要：因子内の低次ホモトピーを保ったまま、直積群の準同型 μ を最後に適用する。
方針：一般テンソルの実区間比較に T の対角と μ の射を前後合成する。
規約：KST Construction A.5 の右辺の augmentation 補正 C(φ)+C(φ′)−C(e_H)。
原典の一般文言との差として P,Q,H,μ,α,β と因子内の入力を明示し、H の可換性を仮定しない。
使われ方：外部 G の同変性の接続と非可換なブロック群への Lemma 4.16 の適用。非同変版だけでは L6c 完了としない。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：非可換標的に対する μ 版 A.5 の非同変な実区間比較。
方針：因子内の厳密化・正規化・差のテンソルの消滅・実 EZ 比較・区間復元を合成する。
規約：KST A.5 の augmentation 補正。φ=μ(α,1)、φ′=μ(1,β)、φ·φ′=μ(α,β)。
原典の可換な H への置換を使わず、ホモトピーの値域を P,Q に保つ。
使われ方：G 同変版の基礎となる実ホモトピー。 -/
def constructionA5 {T P Q H : Type u} [Group T] [Group P] [Group Q] [Group H]
    (d : GroupProductData T P Q H) (m m' : ℕ)
    (hα : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy (groupLinearizedMap d.α) (groupLinearizedMap (1 : T →* P)) m)
    (hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy (groupLinearizedMap d.β) (groupLinearizedMap (1 : T →* Q)) m') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy (groupLinearizedMap d.product)
      (groupLinearizedMap d.left + groupLinearizedMap d.right - groupLinearizedMap (1 : T →* H))
      (m + m' + 1) := by
  let a := linearizedDiagonal (nerve (SingleObj T))
  let b := linearizedGroupProduct d.μ
  have h := linearizedTensorAugmentationMHomotopy hα hβ a b
  have hl : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (groupLinearizedMap d.α) (groupLinearizedMap d.β) ≫ b =
      groupLinearizedMap d.product := linearizedGroupProduct_comp d.μ d.α d.β
  have hr : a ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (groupLinearizedMap d.α) (groupLinearizedMap (1 : T →* Q)) +
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (groupLinearizedMap (1 : T →* P)) (groupLinearizedMap d.β) -
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap (groupLinearizedMap (1 : T →* P))
          (groupLinearizedMap (1 : T →* Q))) ≫ b =
      groupLinearizedMap d.left + groupLinearizedMap d.right - groupLinearizedMap (1 : T →* H) := by
    dsimp only [a, b]
    simp only [Preadditive.comp_add, Preadditive.comp_sub, Preadditive.add_comp, Preadditive.sub_comp,
      Category.assoc]
    rw [linearizedGroupProduct_comp, linearizedGroupProduct_comp, linearizedGroupProduct_comp,
      groupProduct_trivial]
    rfl
  refine { h := h.h, h₀ := ?_, h₁ := ?_ }
  · intro n hn
    exact (h.h₀ n hn).trans (congrArg (fun t ↦ t.app (op ⦋n⦌)) hl)
  · intro n hn
    exact (h.h₁ n hn).trans (congrArg (fun t ↦ t.app (op ⦋n⦌)) hr)

end SerrePositivity.KST.ProExcision

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite KST "Construction A.5" (partial := stronger-hyp) "仮定：離散群の直積を経由する準同型と、因子 P,Q 内でのホモトピーを要求（Lean が強い）。結論：次数 m+m′+1 までの積と増大補正つき二項和の鎖ホモトピー。非被約 C で定値写像を引く形は計画の決定 14 に従う（原典の表示に対し補正あり）。"] _root_.SerrePositivity.KST.ProExcision.constructionA5
