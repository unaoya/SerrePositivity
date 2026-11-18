module

public import SerrePositivity.EInfinity.BarrattEccles.HammockLengthFiltration
public import SerrePositivity.EInfinity.BarrattEccles.HammockGraphProper
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAlternating
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LengthBoundary

/-!
# 任意の可換環上の元の長さ境界と貼り合わせ射

概要：短い語からの包含の像の和と、前の長さ段階への元の射を提供する。
方針：実際の E 代数の graph 図式の proper 性と原像の重なりの回収を代入する。
規約：段階の pushout の普遍性と弱同値不変性は後続。係数環は任意。
使われ方：元の三列の標準射の弱同値性。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.EInfinity.BarrattEccles
variable (A : Type u) [CommRing A] (X Y : (operad A).Algebra)

def algebraHammockLengthBoundary (n : ℕ) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    (algebraHammockGraph A c X Y).Subcomplex :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundary (algebraHammockGraphDiagram A X Y) n c

def algebraHammockLengthBoundaryToStage (n : ℕ) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    (algebraHammockLengthBoundary A X Y n c).toFunctor ⟶ algebraHammockLengthStage A X Y n :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundaryToStage (algebraHammockGraphDiagram_proper A X Y) n c

lemma algebraHammockLengthBoundaryToStage_app (n : ℕ) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word)
    (k : SimplexCategoryᵒᵖ) (x : ((algebraHammockLengthBoundary A X Y n c).toFunctor).obj k)
    {a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (ha : a.length ≤ n) (f : a ⟶ c) (hf : Function.Injective f.orderHom)
    (σ : (algebraHammockGraph A a X Y).obj k)
    (hσ : (algebraHammockGraphMap A f X Y).app k σ = x.val) :
    (algebraHammockLengthBoundaryToStage A X Y n c).app k x =
      (algebraHammockLengthStageInclusion A X Y n a ha).app k σ :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundaryStageValue_eq (algebraHammockGraphDiagram_proper A X Y)
    n c k x ha f hf σ hσ

lemma algebraHammockLengthBoundary_square {n m : ℕ} (h : n ≤ m)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (hc : c.length ≤ m) :
    algebraHammockLengthBoundaryToStage A X Y n c ≫ algebraHammockLengthTransition A X Y h =
      (algebraHammockLengthBoundary A X Y n c).ι ≫
        algebraHammockLengthStageInclusion A X Y m c hc :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.lengthBoundary_square (algebraHammockGraphDiagram_proper A X Y) h c hc

lemma algebraHammockAlternatingGraphMap_mono {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word}
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.IsAlternating a) (f : a ⟶ b) : Mono (algebraHammockGraphMap A f X Y) :=
  algebraHammockGraphMap_mono A f (ha.map_injective f) X Y

end SerrePositivity.EInfinity.BarrattEccles
