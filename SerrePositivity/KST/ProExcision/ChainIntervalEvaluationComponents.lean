module
public import SerrePositivity.KST.ProExcision.IntegerChainInterval
public import SerrePositivity.KST.ProExcision.IntegerTensorFreeDesc
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ChainTensorHomotopy

/-!
# 鎖区間の頂点と辺上のホモトピーの評価

概要：頂点上で二つの端点写像、辺上でホモトピーを評価する実テンソル写像を作る。
方針：第二因子の自由基底上の線形写像から降下させる。
規約：KST Definition A.3、Construction A.5、第一因子の自由性は不要。
使われ方：鎖ホモトピーの全テンソル区間からの実鎖写像。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory HomologicalComplex

/-- 概要：区間の二つの頂点上で二つの端点写像を評価する。
方針：零番目の基底には f、残る一番目には g を指定する。
規約：KST A.3・A.5。使われ方：全テンソル区間の区間次数0の成分。 -/
def chainIntervalEndpointEval {M N : ModuleCat.{u} ℤ} (f g : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensor M (integerIntervalX 0) ⟶ N :=
  integerTensorFreeDesc (fun i : ULift.{u} (Fin 2) ↦ if i.down = 0 then f else g)

/-- 概要：始点の純テンソルの評価は f。
方針：自由基底への降下公式を使う。
規約：KST A.3。使われ方：区間写像の始点。 -/
@[simp] lemma chainIntervalEndpointEval_zero {M N : ModuleCat.{u} ℤ} (f g : M ⟶ N) (m : M) :
    chainIntervalEndpointEval f g (TensorProduct.tmul ℤ m (integerIntervalVertex 0)) = f m := by
  exact integerTensorFreeDesc_generator
    (fun i : ULift.{u} (Fin 2) ↦ if i.down = 0 then f else g) m (ULift.up 0)

/-- 概要：終点の純テンソルの評価は g。
方針：自由基底への降下公式を使う。
規約：KST A.3。使われ方：区間写像の終点。 -/
@[simp] lemma chainIntervalEndpointEval_one {M N : ModuleCat.{u} ℤ} (f g : M ⟶ N) (m : M) :
    chainIntervalEndpointEval f g (TensorProduct.tmul ℤ m (integerIntervalVertex 1)) = g m := by
  exact integerTensorFreeDesc_generator
    (fun i : ULift.{u} (Fin 2) ↦ if i.down = 0 then f else g) m (ULift.up 1)

/-- 概要：区間の辺上で指定された一段上の線形写像を評価する。
方針：唯一の辺の基底に写像を指定する。
規約：KST A.3・A.5。使われ方：全テンソル区間の区間次数1の成分。 -/
def chainIntervalEdgeEval {M N : ModuleCat.{u} ℤ} (h : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensor M (integerIntervalX 1) ⟶ N := integerTensorFreeDesc (fun _ ↦ h)

/-- 概要：辺の純テンソルの評価は指定した写像。
方針：自由基底への降下公式を使う。
規約：KST A.3。使われ方：ホモトピーの符号付き成分の評価。 -/
@[simp] lemma chainIntervalEdgeEval_edge {M N : ModuleCat.{u} ℤ} (h : M ⟶ N) (m : M) :
    chainIntervalEdgeEval h (TensorProduct.tmul ℤ m integerIntervalEdge) = h m :=
  integerTensorFreeDesc_generator _ _ _

/-- 概要：鎖ホモトピーを鎖区間の各二重次数で評価する。
方針：頂点は端点写像、辺は (−1)^(p+1) 倍のホモトピー、高次は零。
規約：KST A.3・A.5、辺の境界は終点−始点。鎖写像性は別工程。
使われ方：全テンソルの降下写像の構成。 -/
def chainHomotopyIntervalBidegree {K L : ChainComplex (ModuleCat.{u} ℤ) ℕ}
    {f g : K ⟶ L} (H : Homotopy f g) (p q n : ℕ) (hpq : p + q = n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensor (K.X p) (integerChainInterval.X q) ⟶ L.X n := by
  subst n
  cases q with
  | zero => exact chainIntervalEndpointEval (f.f p) (g.f p)
  | succ q =>
    cases q with
    | zero => exact (-1 : ℤ) ^ (p + 1) • chainIntervalEdgeEval (H.hom p (p + 1))
    | succ q => exact 0

end SerrePositivity.KST.ProExcision
