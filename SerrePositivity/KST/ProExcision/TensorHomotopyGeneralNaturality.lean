module
public import SerrePositivity.KST.ProExcision.TensorHomotopyComponents
public import SerrePositivity.KST.ProExcision.ChainHomotopySquare

/-!
# 二つの一般の鎖ホモトピーの全テンソルの自然性

概要：両因子のホモトピーの自然性と必要な端点の正方形から全テンソルの自然性を導く。
方針：各二重次数の水平・垂直の二成分でテンソル写像の合成則を使う。
規約：KST Construction A.5、恒等への収縮に限定しない。
使われ方：因子内の厳密化比較を外部群の作用と可換にテンソルへ移す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory HomologicalComplex

/-- 概要：二因子の自然な全鎖比較は全テンソルでも自然。
方針：水平成分では第二因子の始点、垂直成分では第一因子の終点の自然性を使う。
規約：KST A.5、構成済みの比較を移送する一般補題。
使われ方：厳密化した因子への実全テンソル比較の同変性。 -/
lemma chainIntegerTensorHomotopy_naturality
    {K K' L L' M M' N N' : ChainComplex (ModuleCat.{u} ℤ) ℕ}
    {f F : K ⟶ L} {f' F' : K' ⟶ L'} {g G : M ⟶ N} {g' G' : M' ⟶ N'}
    (h : Homotopy f F) (h' : Homotopy f' F') (k : Homotopy g G) (k' : Homotopy g' G')
    (a : K ⟶ K') (b : M ⟶ M') (c : L ⟶ L') (d : N ⟶ N')
    (hF : a ≫ F' = F ≫ c) (hg : b ≫ g' = g ≫ d)
    (hh : ChainHomotopySquare a c h h') (hk : ChainHomotopySquare b d k k') (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap a b).f n ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorHomotopy h' k').hom n (n + 1) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorHomotopy h k).hom n (n + 1) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap c d).f (n + 1) := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ι_chainIntegerTensorMap, Category.assoc, ι_chainIntegerTensorHomotopy]
  rw [← Category.assoc (ιMapBifunctor K M _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorBifunctor (.down ℕ) p q n hpq),
    ι_chainIntegerTensorHomotopy]
  simp only [Preadditive.comp_add, Preadditive.comp_zsmul, Preadditive.add_comp,
    Preadditive.zsmul_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ι_chainIntegerTensorMap]
  have hgb := congrArg (fun t ↦ t.f q) hg
  change b.f q ≫ g'.f q = g.f q ≫ d.f q at hgb
  have hFa := congrArg (fun t ↦ t.f p) hF
  change a.f p ≫ F'.f p = F.f p ≫ c.f p at hFa
  congr 1
  · rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_comp, hh p, hgb,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_comp, Category.assoc]
  · congr 1
    rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_comp, hFa, hk q,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap_comp, Category.assoc]

end SerrePositivity.KST.ProExcision
