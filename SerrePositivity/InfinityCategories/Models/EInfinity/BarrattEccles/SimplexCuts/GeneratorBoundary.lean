module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NormalizedGenerators
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.BoundaryCuts

/-!
模型。文献の定義との比較は後で
# BF 切断で使う同じ正規化生成元の微分

Berger–Fresse §2.2.6–7。既存の正規化鎖の境界を q ↦ −q の延長で読む。
M14 L09a の前提計算1。単体の面の符号や正規化射を選び直さない。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.HomologicalComplex
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- gen_d の証明の分割：同じ延長の負自然数次数での微分の式。 -/
lemma chains_d_neg (S : SSet.{0}) (p q : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).d (-(p : ℤ)) (-(q : ℤ)) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chainsXIso A S p).hom ≫ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A S).d p q ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chainsXIso A S q).inv :=
  extend_d_eq (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A S) ComplexShape.embeddingDownNat rfl rfl

/-- 同じ正規化生成元の交代面による境界（BF §2.2.6）。 -/
lemma gen_d (S : SSet.{0}) (q : ℕ) (x : S _⦋q + 1⦌) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).d (-((q + 1 : ℕ) : ℤ)) (-(q : ℤ)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S (q + 1) x) =
      ∑ i : Fin (q + 2), (-1 : ℤ)^i.val • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S q (S.δ i x) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains_d_neg]
  change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chainsXIso A S q).toLinearEquiv.symm
    ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A S).d (q + 1) q
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chainsXIso A S (q + 1)).toLinearEquiv
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chainsXIso A S (q + 1)).toLinearEquiv.symm
          (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A S (q + 1) x)))) = _
  rw [LinearEquiv.apply_symm_apply, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator_d]
  simp only [map_sum, map_zsmul, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen]
  rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
