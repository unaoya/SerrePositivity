module
public import SerrePositivity.KST.ProExcision.ChainIntervalTensorDifferential
public import SerrePositivity.KST.ProExcision.ChainIntervalEdgeAdditivity
public import SerrePositivity.KST.ProExcision.ChainIntervalHomotopySigns

/-!
# 鎖ホモトピーによる全テンソル区間からの実鎖写像

概要：頂点・符号付き辺の評価は全テンソルの微分と可換。
方針：区間次数0では端点の鎖写像性、次数1ではホモトピー等式、次数2以上では始域の自明性を使う。
規約：KST Definition A.3、Construction A.5、辺の境界は終点−始点。
使われ方：Moore 複体の鎖ホモトピーから実単体的な区間写像への復元。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory HomologicalComplex
variable {K L : ChainComplex (ModuleCat.{u} ℤ) ℕ} {f g : K ⟶ L} (H : Homotopy f g)

/-- 概要：区間次数0の評価は全テンソルの微分と可換。
方針：垂直微分は零、水平微分は二つの端点の鎖写像性。
規約：KST A.3・A.5。使われ方：全複体の頂点成分の検証。 -/
lemma chainHomotopyInterval_comm_vertex (n : ℕ) :
    chainHomotopyIntervalBidegree H (n + 1) 0 (n + 1) rfl ≫ L.d (n + 1) n =
    ιMapBifunctor K integerChainInterval _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ)
        (n + 1) 0 (n + 1) rfl ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensor K integerChainInterval).d (n + 1) n ≫ chainHomotopyIntervalApp H n := by
  rw [mapBifunctor.d_eq, Preadditive.add_comp, Preadditive.comp_add,
    chainInterval_ι_D₁_succ H (show n + 0 = n from rfl),
    chainInterval_ι_D₂_zero H (show (n + 1) + 0 = n + 1 from rfl)]
  simp only [add_zero]
  change chainIntervalEndpointEval (f.f (n + 1)) (g.f (n + 1)) ≫ L.d (n + 1) n =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap (K.d (n + 1) n) (𝟙 (integerIntervalX 0)) ≫
      chainIntervalEndpointEval (f.f n) (g.f n)
  exact chainIntervalEndpointEval_comm f g n

/-- 概要：区間次数1・第一因子零次の評価は微分と可換。
方針：辺上の負のホモトピーの境界が終点−始点に一致することを使う。
規約：KST A.3・A.5、非被約な零次を含む。
使われ方：全複体の辺成分の基底。 -/
lemma chainHomotopyInterval_comm_edge_zero :
    chainHomotopyIntervalBidegree H 0 1 1 rfl ≫ L.d 1 0 =
    ιMapBifunctor K integerChainInterval _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) 0 1 1 rfl ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensor K integerChainInterval).d 1 0 ≫ chainHomotopyIntervalApp H 0 := by
  rw [mapBifunctor.d_eq, Preadditive.add_comp, Preadditive.comp_add,
    chainInterval_ι_D₁_zero H (show 0 + 1 = 1 from rfl),
    chainInterval_ι_D₂_succ H (show 0 + 0 = 0 from rfl)]
  simp only [zero_add, pow_zero, one_smul]
  change ((-1 : ℤ) ^ 1 • chainIntervalEdgeEval (H.hom 0 1)) ≫ L.d 1 0 =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap (𝟙 (K.X 0)) integerIntervalBoundary ≫
      chainIntervalEndpointEval (f.f 0) (g.f 0)
  rw [Preadditive.zsmul_comp, ← chainIntervalEdgeEval_comp,
    ← chainIntervalEdgeEval_zsmul, chainIntervalHomotopySign_zero,
    chainIntervalEndpointEval_boundary]

/-- 概要：区間次数1・第一因子正次数の評価は微分と可換。
方針：水平成分と垂直成分を符号付きホモトピー等式へ同定する。
規約：KST A.3・A.5、辺の符号は (−1)^(p+2)。
使われ方：全複体の辺成分の正次数。 -/
lemma chainHomotopyInterval_comm_edge_succ (p : ℕ) :
    chainHomotopyIntervalBidegree H (p + 1) 1 (p + 2) rfl ≫ L.d (p + 2) (p + 1) =
    ιMapBifunctor K integerChainInterval _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ)
        (p + 1) 1 (p + 2) rfl ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensor K integerChainInterval).d (p + 2) (p + 1) ≫
        chainHomotopyIntervalApp H (p + 1) := by
  rw [mapBifunctor.d_eq, Preadditive.add_comp, Preadditive.comp_add,
    chainInterval_ι_D₁_succ H (show p + 1 = p + 1 from rfl),
    chainInterval_ι_D₂_succ H (show (p + 1) + 0 = p + 1 from rfl)]
  change ((-1 : ℤ) ^ (p + 2) • chainIntervalEdgeEval (H.hom (p + 1) (p + 2))) ≫
      L.d (p + 2) (p + 1) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap (K.d (p + 1) p) (𝟙 (integerIntervalX 1)) ≫
        ((-1 : ℤ) ^ (p + 1) • chainIntervalEdgeEval (H.hom p (p + 1))) +
      (-1 : ℤ) ^ (p + 1) • (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap (𝟙 (K.X (p + 1))) integerIntervalBoundary ≫
        chainIntervalEndpointEval (f.f (p + 1)) (g.f (p + 1)))
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  have he := congrArg (chainIntervalEdgeEval (M := K.X (p + 1)) (N := L.X (p + 1)))
    (chainIntervalHomotopySign_succ H p)
  rw [chainIntervalEdgeEval_zsmul, chainIntervalEdgeEval_comp, chainIntervalEdgeEval_add,
    chainIntervalEdgeEval_zsmul, chainIntervalEdgeEval_precomp, chainIntervalEdgeEval_zsmul,
    ← chainIntervalEndpointEval_boundary] at he
  exact he

/-- 概要：全テンソル鎖区間の評価は各全次数で微分と可換。
方針：標準包含で検出し、区間次数0、1、自明な高次の三場合を使う。
規約：KST Definition A.3、Construction A.5、実鎖複体の等式。
使われ方：鎖区間の評価を実鎖写像へ束ねる。 -/
theorem chainHomotopyInterval_comm (n : ℕ) :
    chainHomotopyIntervalApp H (n + 1) ≫ L.d (n + 1) n =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensor K integerChainInterval).d (n + 1) n ≫ chainHomotopyIntervalApp H n := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  rw [← Category.assoc, ι_chainHomotopyIntervalApp]
  change p + q = n + 1 at hpq
  cases q with
  | zero =>
    have hp : p = n + 1 := by omega
    subst p
    exact chainHomotopyInterval_comm_vertex H n
  | succ q =>
    cases q with
    | zero =>
      have hp : p = n := by omega
      subst n
      cases p with
      | zero => exact chainHomotopyInterval_comm_edge_zero H
      | succ p => exact chainHomotopyInterval_comm_edge_succ H p
    | succ q =>
      exact (integerTensor_punit_hom_zero _).trans (integerTensor_punit_hom_zero _).symm

/-- 概要：鎖ホモトピーによる全テンソル鎖区間からの実鎖写像。
方針：頂点・符号付き辺の評価に検証済みの微分可換性を付ける。
規約：KST Definition A.3、Construction A.5、存在を追加仮定にしない。
使われ方：単体的区間からの AW と Dold–Kan による復元。 -/
def chainHomotopyInterval : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensor K integerChainInterval ⟶ L :=
  ChainComplex.ofHom (chainHomotopyIntervalApp H) (chainHomotopyInterval_comm H)

end SerrePositivity.KST.ProExcision
