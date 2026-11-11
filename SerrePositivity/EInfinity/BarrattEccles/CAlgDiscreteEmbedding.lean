module

public import SerrePositivity.EInfinity.BarrattEccles.CAlgAlgebraSource

/-!
# 元の離散可換代数から既存 CAlg_R への実 ∞ 関手

概要：元の離散 E 代数関手と同じ全代数の局所化源を合成する。
方針：元の通常の nerve と全単体の置換写像を使う。
規約：既存 discreteCAlgVertex へ全頂点の同型を保持する。
使われ方：離散入力の U 比較。離散性の特徴付けは後続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial
variable (A : Type u) [CommRing A]

def discreteCAlgEmbedding : nerve (CommAlgCat.{u} A) ⟶ CAlg_R A :=
  nerveMap (discreteAlgebraFunctor A) ≫ algebraCAlgSource A

def discreteCAlgEmbedding_vertexIso (B : CommAlgCat.{u} A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((discreteCAlgEmbedding A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex B))
      (discreteCAlgVertex A B) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((algebraCAlgSource A).app (Opposite.op ⦋0⦌)
    ((nerveMap (discreteAlgebraFunctor A)).app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ B))) _
  rw [nerveMap_app_mk₀]
  exact algebraCAlgSource_vertexIso A ((discreteAlgebraFunctor A).obj B)

def discreteCAlgEmbedding_forgetIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (discreteCAlgEmbedding A ≫ cAlgForgetDerived A)
      (nerveMap (discreteAlgebraFunctor A) ≫ algebraCAlgReplacementNerve A ≫
        cofibrantAlgebraUnderlyingDerivedSource A) := by
  simpa only [discreteCAlgEmbedding, Category.assoc] using
    (algebraCAlgSource_forgetIso A).precomp (nerveMap (discreteAlgebraFunctor A))

end SerrePositivity.EInfinity.BarrattEccles
