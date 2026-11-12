module
public import SerrePositivity.KST.ProExcision.ChainIntervalEvaluationComponents
public import Mathlib.Tactic.FinCases

/-!
# 区間の頂点・辺の評価の自然性

概要：二つの端点と辺の実テンソル評価を前後合成と区間の境界へ接続する。
方針：第二因子の基底との純テンソルに評価して線形写像の正方形を使う。
規約：KST Definition A.3、Construction A.5、第一因子の自由性は不要。
使われ方：全テンソルの微分との可換性と外部作用の同変性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory HomologicalComplex

/-- 概要：二つの端点の可換な正方形は区間の頂点の評価でも可換。
方針：二つの頂点の基底上で元の正方形を評価する。
規約：KST A.3・A.5。使われ方：端点写像の微分可換性と自然性。 -/
lemma chainIntervalEndpointEval_naturality {M M' N N' : ModuleCat.{u} ℤ}
    (f g : M ⟶ N) (f' g' : M' ⟶ N') (a : M ⟶ M') (b : N ⟶ N')
    (hf : a ≫ f' = f ≫ b) (hg : a ≫ g' = g ≫ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap a (𝟙 (integerIntervalX 0)) ≫ chainIntervalEndpointEval f' g' =
      chainIntervalEndpointEval f g ≫ b := by
  apply integerTensor_free_hom_ext
  intro m i
  rcases i with ⟨i⟩
  fin_cases i
  · change chainIntervalEndpointEval f' g' (TensorProduct.tmul ℤ (a m) (integerIntervalVertex 0)) =
      b (chainIntervalEndpointEval f g (TensorProduct.tmul ℤ m (integerIntervalVertex 0)))
    rw [chainIntervalEndpointEval_zero, chainIntervalEndpointEval_zero]
    exact congrArg (fun t ↦ t m) hf
  · change chainIntervalEndpointEval f' g' (TensorProduct.tmul ℤ (a m) (integerIntervalVertex 1)) =
      b (chainIntervalEndpointEval f g (TensorProduct.tmul ℤ m (integerIntervalVertex 1)))
    rw [chainIntervalEndpointEval_one, chainIntervalEndpointEval_one]
    exact congrArg (fun t ↦ t m) hg

/-- 概要：辺の評価は可換な線形写像の正方形を保つ。
方針：唯一の辺の基底上で元の正方形を評価する。
規約：KST A.3・A.5。使われ方：ホモトピー成分の前後合成。 -/
lemma chainIntervalEdgeEval_naturality {M M' N N' : ModuleCat.{u} ℤ}
    (h : M ⟶ N) (h' : M' ⟶ N') (a : M ⟶ M') (b : N ⟶ N')
    (hh : a ≫ h' = h ≫ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap a (𝟙 (integerIntervalX 1)) ≫ chainIntervalEdgeEval h' =
      chainIntervalEdgeEval h ≫ b := by
  apply integerTensor_free_hom_ext
  intro m i
  rcases i with ⟨⟨⟩⟩
  change chainIntervalEdgeEval h' (TensorProduct.tmul ℤ (a m) integerIntervalEdge) =
    b (chainIntervalEdgeEval h (TensorProduct.tmul ℤ m integerIntervalEdge))
  rw [chainIntervalEdgeEval_edge, chainIntervalEdgeEval_edge]
  exact congrArg (fun t ↦ t m) hh

/-- 概要：二つの鎖写像の区間頂点上の評価は微分と可換。
方針：二つの鎖写像の微分可換性を端点評価の自然性へ適用する。
規約：KST A.3・A.5。使われ方：区間次数0の鎖写像条件。 -/
lemma chainIntervalEndpointEval_comm {K L : ChainComplex (ModuleCat.{u} ℤ) ℕ}
    (f g : K ⟶ L) (n : ℕ) :
    chainIntervalEndpointEval (f.f (n + 1)) (g.f (n + 1)) ≫ L.d (n + 1) n =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap (K.d (n + 1) n) (𝟙 (integerIntervalX 0)) ≫
        chainIntervalEndpointEval (f.f n) (g.f n) :=
  (chainIntervalEndpointEval_naturality _ _ _ _ _ _
    (f.comm (n + 1) n).symm (g.comm (n + 1) n).symm).symm

/-- 概要：区間の辺の境界の後の端点評価は二つの端点写像の差。
方針：辺の境界を終点−始点へ展開し、純テンソルと評価の差へ分配する。
規約：KST A.3・A.5。使われ方：区間次数1のホモトピー等式。 -/
lemma chainIntervalEndpointEval_boundary {M N : ModuleCat.{u} ℤ} (f g : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap (𝟙 M) integerIntervalBoundary ≫ chainIntervalEndpointEval f g =
      chainIntervalEdgeEval (g - f) := by
  apply integerTensor_free_hom_ext
  intro m i
  rcases i with ⟨⟨⟩⟩
  change chainIntervalEndpointEval f g
      (TensorProduct.tmul ℤ m (integerIntervalBoundary integerIntervalEdge)) =
    chainIntervalEdgeEval (g - f) (TensorProduct.tmul ℤ m integerIntervalEdge)
  rw [integerIntervalBoundary_edge, TensorProduct.tmul_sub, map_sub,
    chainIntervalEndpointEval_one, chainIntervalEndpointEval_zero, chainIntervalEdgeEval_edge]
  rfl

end SerrePositivity.KST.ProExcision
