module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedHomDiagonal
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanAnodyneLocalization
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalLocalizedEquivalence
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：元の coslice fiber から twisted arrow の両端固定の写像空間への主比較は同値。
方針：各行の同値を anodyne 局所化へ送り、二重単体図式の対角の定理と Kan 判定で戻す。
規約：結論は元の cosliceTwistedHomMap そのもので、値宇宙のモデル構造を仮定しない。
使われ方：元の表現可能 right fibration と Yoneda 対象前層の比較。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.SimplicialModel
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

/-- 元の coslice の主比較は、全ての quasicategory と両端に対して実際の同値。 -/
@[kerodon 03K1]
lemma cosliceTwistedHomMap_isQCatEquivalence {C : SSet.{u}} [Quasicategory C]
    (x y : C _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceTwistedHomMap x y) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isQCatEquivalence_of_anodyneQ_isIso
  have hf : ∀ n, IsIso (AnodyneHomotopy.anodyneQ.map
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedHomRowsAugmentation x y).app n)) := by
    rintro ⟨⟨n⟩⟩
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedHomRowAugment_isQCatEquivalence x y n).anodyneQ_isIso
  have : IsIso (AnodyneHomotopy.anodyneQ.map
      (SerrePositivity.BisimplicialModel.diagonal.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedHomRowsAugmentation x y))) :=
    SerrePositivity.BisimplicialModel.localized_diagonal_map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedHomRowsAugmentation x y) hf
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceTwistedHomMap_eq_diagonal, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp]
  infer_instance

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
