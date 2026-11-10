module
public import SerrePositivity.KST.ProExcision.ChainIntervalEvaluationChainMap
public import SerrePositivity.KST.ProExcision.ChainHomotopySquare

/-!
# 全テンソル鎖区間の実評価の自然性

概要：二つの端点と鎖ホモトピーの自然な正方形から区間評価の自然性を導く。
方針：全複体の標準包含で頂点・辺・自明な高次の三場合へ分ける。
規約：KST Definition A.3、Construction A.5、構成済みホモトピーに適用する移送補題。
使われ方：単体的区間の復元と外部群同変性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory HomologicalComplex

/-- 概要：二つの端点とホモトピーの自然性は全テンソル区間の実鎖写像の自然性を与える。
方針：区間次数0は端点評価、次数1はホモトピー評価、高次は始域の自明性を使う。
規約：KST A.3・A.5、ホモトピーの存在や同変性を追加の結論仮定にしない一般の移送。
使われ方：構成済みの正規化比較を外部群の作用と可換に復元する。 -/
lemma chainHomotopyInterval_naturality
    {K K' L L' : ChainComplex (ModuleCat.{u} ℤ) ℕ}
    {f g : K ⟶ L} {f' g' : K' ⟶ L'} (H : Homotopy f g) (H' : Homotopy f' g')
    (a : K ⟶ K') (b : L ⟶ L') (hf : a ≫ f' = f ≫ b) (hg : a ≫ g' = g ≫ b)
    (hH : ChainHomotopySquare a b H H') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap a (𝟙 integerChainInterval) ≫ chainHomotopyInterval H' =
      chainHomotopyInterval H ≫ b := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply mapBifunctor.hom_ext
  intro p q hpq
  simp only [comp_f]
  change ιMapBifunctor K integerChainInterval _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) p q n hpq ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap a (𝟙 integerChainInterval)).f n ≫ chainHomotopyIntervalApp H' n) =
    ιMapBifunctor K integerChainInterval _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) p q n hpq ≫
      (chainHomotopyIntervalApp H n ≫ b.f n)
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ι_chainIntegerTensorMap, Category.assoc,
    ι_chainHomotopyIntervalApp, ← Category.assoc, ι_chainHomotopyIntervalApp]
  change p + q = n at hpq
  cases q with
  | zero =>
    have hn : n = p := by omega
    subst n
    change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap (a.f p) (𝟙 (integerIntervalX 0)) ≫
        chainIntervalEndpointEval (f'.f p) (g'.f p) =
      chainIntervalEndpointEval (f.f p) (g.f p) ≫ b.f p
    have hfn := congrArg (fun k ↦ k.f p) hf
    have hgn := congrArg (fun k ↦ k.f p) hg
    exact chainIntervalEndpointEval_naturality _ _ _ _ _ _ hfn hgn
  | succ q =>
    cases q with
    | zero =>
      have hn : n = p + 1 := hpq.symm
      subst n
      change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap (a.f p) (𝟙 (integerIntervalX 1)) ≫
          ((-1 : ℤ) ^ (p + 1) • chainIntervalEdgeEval (H'.hom p (p + 1))) =
        ((-1 : ℤ) ^ (p + 1) • chainIntervalEdgeEval (H.hom p (p + 1))) ≫ b.f (p + 1)
      rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp]
      congr 1
      exact chainIntervalEdgeEval_naturality _ _ _ _ (hH p)
    | succ q =>
      exact (integerTensor_punit_hom_zero _).trans (integerTensor_punit_hom_zero _).symm

end SerrePositivity.KST.ProExcision
