module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantSourceRoofCornerEvaluation
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ProductSimplexElementProjectionWeak
public import SerrePositivity.EInfinity.BarrattEccles.SourceFramePrecompose
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.WeakArrowActionEquivalences

/-!
# 元の積単体から指定次数の hammock Hom への弱な基準射

概要：元の積単体を第一成分へ送り、元の高次比較と D_n→X の前合成を接続する。
方針：全単体の第一射影と保存済みの sourceFrame 比較・元の弱 augmentation を使う。
規約：任意可換環・元の M・元の D_n→X・同じ reduced hammock を保持する。
使われ方：実 ProductHomMap との全ホモトピーを照合する基準射。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits Opposite _root_.HomotopicalAlgebra
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)
  (b : (cofibrantSourceRoofTarget A X Y) _⦋0⦌)

lemma cofibrantSourceRoofProductFirstNerve_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (cofibrantSourceRoofProductFirstNerve A X Y b) :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ProductSimplexLiftedOver.firstNerveMap_weak _ _

def cofibrantSourceRoofProductHammockMap :
    nerve (cofibrantSourceRoofProductElements A X Y b) ⟶ algebraReducedHammock A X.obj Y.obj :=
  cofibrantSourceRoofProductFirstNerve A X Y b ≫ sourceFrameReducedHammockNerveMap A X.obj Y.obj

lemma cofibrantSourceRoofProductHammockMap_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (cofibrantSourceRoofProductHammockMap A X Y b) :=
  (cofibrantSourceRoofProductFirstNerve_weak A X Y b).comp
    (sourceFrameReducedHammockNerveMap_weak A X.obj Y.obj)

def cofibrantSourceRoofDegreePrecompose : algebraReducedHammock A X.obj Y.obj ⟶
    algebraReducedHammock A (cofibrantSourceRoofDegreeAlgebra A X Y b).obj Y.obj :=
  algebraReducedHammockPrecompose A Y.obj
    ((cofibrantSourceFrameAugmentation A X).app
      (ULift.down (cofibrantSourceRoofDegree A X Y b))).hom

lemma cofibrantSourceRoofDegreePrecompose_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (cofibrantSourceRoofDegreePrecompose A X Y b) := by
  let := modelCategory A
  let n := ULift.down (cofibrantSourceRoofDegree A X Y b)
  let f := ((cofibrantSourceFrameAugmentation A X).app n).hom
  have hf : weakEquivalences (operad A).Algebra f :=
    cofibrantSourceFrameAugmentation_weak A X n
  have h₀ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (algebraHammockReductionIso A X.obj Y.obj).symm).isWeakHomotopyEquivalence
  have h₁ := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.WeakArrow.precompose_forward_isWeakHomotopyEquivalence f hf Y.obj
  have h₂ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (algebraHammockReductionIso A
    (cofibrantSourceRoofDegreeAlgebra A X Y b).obj Y.obj)).isWeakHomotopyEquivalence
  exact h₀.comp (h₁.comp h₂)

def cofibrantSourceRoofProductDegreeHammockMap :
    nerve (cofibrantSourceRoofProductElements A X Y b) ⟶
      algebraReducedHammock A (cofibrantSourceRoofDegreeAlgebra A X Y b).obj Y.obj :=
  cofibrantSourceRoofProductHammockMap A X Y b ≫ cofibrantSourceRoofDegreePrecompose A X Y b

lemma cofibrantSourceRoofProductDegreeHammockMap_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (cofibrantSourceRoofProductDegreeHammockMap A X Y b) :=
  (cofibrantSourceRoofProductHammockMap_weak A X Y b).comp
    (cofibrantSourceRoofDegreePrecompose_weak A X Y b)

end SerrePositivity.EInfinity.BarrattEccles
