module
public import SerrePositivity.KST.ProExcision.ChainIntervalEvaluationNaturality

/-!
# 鎖区間の辺の評価の加法性

概要：辺上の線形写像の加減法と整数倍を辺の評価へ移す。
方針：唯一の辺の基底上で加法性を確認し、加法群の準同型として束ねる。
規約：KST Definition A.3、Construction A.5。
使われ方：符号付きホモトピー等式を全テンソルの微分へ移す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory

/-- 概要：零写像の辺上の評価は零。
方針：唯一の辺の基底上で計算する。
規約：KST A.3・A.5。使われ方：辺の評価の加法準同型。 -/
lemma chainIntervalEdgeEval_zero (M N : ModuleCat.{u} ℤ) :
    chainIntervalEdgeEval (0 : M ⟶ N) = 0 := by
  apply integerTensor_free_hom_ext
  intro m i
  rcases i with ⟨⟨⟩⟩
  change chainIntervalEdgeEval (0 : M ⟶ N) (TensorProduct.tmul ℤ m integerIntervalEdge) = _
  rw [chainIntervalEdgeEval_edge]
  rfl

/-- 概要：二つの線形写像の和の辺上の評価は二つの評価の和。
方針：唯一の辺の基底上で計算する。
規約：KST A.3・A.5。使われ方：ホモトピー等式の加法性の移送。 -/
lemma chainIntervalEdgeEval_add {M N : ModuleCat.{u} ℤ} (h k : M ⟶ N) :
    chainIntervalEdgeEval (h + k) = chainIntervalEdgeEval h + chainIntervalEdgeEval k := by
  apply integerTensor_free_hom_ext
  intro m i
  rcases i with ⟨⟨⟩⟩
  change chainIntervalEdgeEval (h + k) (TensorProduct.tmul ℤ m integerIntervalEdge) =
    chainIntervalEdgeEval h (TensorProduct.tmul ℤ m integerIntervalEdge) +
      chainIntervalEdgeEval k (TensorProduct.tmul ℤ m integerIntervalEdge)
  rw [chainIntervalEdgeEval_edge, chainIntervalEdgeEval_edge, chainIntervalEdgeEval_edge]
  rfl

/-- 概要：辺の評価を線形写像の加法群間の準同型として束ねる。
方針：検証済みの零と和の保存を使う。
規約：KST A.3・A.5、整数倍も自動的に保つ。
使われ方：符号付き鎖ホモトピー等式の移送。 -/
def chainIntervalEdgeEvalAddHom (M N : ModuleCat.{u} ℤ) :
    (M ⟶ N) →+ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensor M (integerIntervalX 1) ⟶ N) where
  toFun := chainIntervalEdgeEval
  map_zero' := chainIntervalEdgeEval_zero M N
  map_add' := chainIntervalEdgeEval_add

/-- 概要：辺の評価は線形写像の整数倍を保つ。
方針：評価の加法準同型の整数倍保存を使う。
規約：KST A.3・A.5。使われ方：区間のホモトピーの符号の移送。 -/
lemma chainIntervalEdgeEval_zsmul {M N : ModuleCat.{u} ℤ} (a : ℤ) (h : M ⟶ N) :
    chainIntervalEdgeEval (a • h) = a • chainIntervalEdgeEval h :=
  (chainIntervalEdgeEvalAddHom M N).map_zsmul a h

/-- 概要：辺の評価は後合成と可換。
方針：第一因子の恒等写像を用いて辺評価の自然性を適用する。
規約：KST A.3・A.5。使われ方：ホモトピーの後の微分。 -/
lemma chainIntervalEdgeEval_comp {M N P : ModuleCat.{u} ℤ} (h : M ⟶ N) (b : N ⟶ P) :
    chainIntervalEdgeEval (h ≫ b) = chainIntervalEdgeEval h ≫ b := by
  have he := chainIntervalEdgeEval_naturality h (h ≫ b) (𝟙 M) b (by rw [Category.id_comp])
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_id, Category.id_comp] at he
  exact he

/-- 概要：辺の評価は第一因子からの前合成と可換。
方針：終域の恒等写像を用いて辺評価の自然性を適用する。
規約：KST A.3・A.5。使われ方：微分の後の低次ホモトピー。 -/
lemma chainIntervalEdgeEval_precomp {M N P : ModuleCat.{u} ℤ} (a : M ⟶ N) (h : N ⟶ P) :
    chainIntervalEdgeEval (a ≫ h) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap a (𝟙 (integerIntervalX 1)) ≫ chainIntervalEdgeEval h := by
  have he := chainIntervalEdgeEval_naturality (a ≫ h) h a (𝟙 P) (by rw [Category.comp_id])
  rw [Category.comp_id] at he
  exact he.symm

end SerrePositivity.KST.ProExcision
