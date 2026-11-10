module
public import SerrePositivity.KST.ProExcision.ChainIntervalEvaluationComponents

/-!
# 全テンソル鎖区間からの降下写像

概要：頂点と辺上で指定したホモトピーの評価を全次数の成分写像へ束ねる。
方針：全テンソルの標準余積の普遍性を使う。
規約：KST Definition A.3、Construction A.5、鎖写像性はこの成分構成と別に証明する。
使われ方：単体的なテンソル区間射への復元の実鎖写像を作る。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory HomologicalComplex

/-- 概要：鎖区間の全テンソルをホモトピーで評価する全次数の成分。
方針：二重次数の端点・辺・零の成分を全複体の余積から降下する。
規約：KST A.3・A.5、実成分の構成であり微分可換性の仮定を含めない。
使われ方：全テンソル区間からの実鎖写像の候補成分。 -/
def chainHomotopyIntervalApp {K L : ChainComplex (ModuleCat.{u} ℤ) ℕ}
    {f g : K ⟶ L} (H : Homotopy f g) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensor K integerChainInterval).X n ⟶ L.X n :=
  mapBifunctorDesc (fun p q h ↦ chainHomotopyIntervalBidegree H p q n h)

/-- 概要：区間の全次数の評価を標準包含へ制限すると二重次数の評価になる。
方針：全複体の余積の降下写像の評価公式を使う。
規約：KST A.3・A.5。使われ方：微分可換性を端点・辺・零の成分に分ける。 -/
@[reassoc (attr := simp)] lemma ι_chainHomotopyIntervalApp
    {K L : ChainComplex (ModuleCat.{u} ℤ) ℕ} {f g : K ⟶ L}
    (H : Homotopy f g) (p q n : ℕ)
    (h : ComplexShape.π (.down ℕ) (.down ℕ) (.down ℕ) (p, q) = n) :
    ιMapBifunctor K integerChainInterval _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) p q n h ≫
      chainHomotopyIntervalApp H n = chainHomotopyIntervalBidegree H p q n h :=
  ι_mapBifunctorDesc _ _ _ _

/-- 概要：自明な第二因子のテンソルから出る全ての線形写像は零。
方針：第二因子の元は零であり、全ての純テンソルが零になる。
規約：KST A.3・A.5、任意の第一因子で成立。
使われ方：区間次数が二次以上の微分条件の消去。 -/
lemma integerTensor_punit_hom_zero {M N : ModuleCat.{u} ℤ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensor M (ModuleCat.of ℤ PUnit.{u + 1}) ⟶ N) : f = 0 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensor_pure_hom_ext
  intro x y
  have hy : y = 0 := Subsingleton.elim _ _
  rw [hy, TensorProduct.tmul_zero]
  simp only [map_zero]

end SerrePositivity.KST.ProExcision
