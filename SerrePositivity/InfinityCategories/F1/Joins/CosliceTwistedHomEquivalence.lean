module

public import SerrePositivity.InfinityCategories.F1.TwistedArrow.TwistedHomDiagonal
public import SerrePositivity.InfinityCategories.F1.KanModels.KanAnodyneLocalization
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalLocalizedEquivalence

/-!
概要：元の coslice fiber から twisted arrow の両端固定の写像空間への主比較は同値。
方針：各行の同値を anodyne 局所化へ送り、二重単体図式の対角の定理と Kan 判定で戻す。
規約：結論は元の cosliceTwistedHomMap そのもので、値宇宙のモデル構造を仮定しない。
使われ方：元の表現可能 right fibration と Yoneda 対象前層の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.SimplicialModel
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 元の coslice の主比較は、全ての quasicategory と両端に対して実際の同値。 -/
lemma cosliceTwistedHomMap_isQCatEquivalence {C : SSet.{u}} [Quasicategory C]
    (x y : C _⦋0⦌) : IsQCatEquivalence (cosliceTwistedHomMap x y) := by
  apply isQCatEquivalence_of_anodyneQ_isIso
  have hf : ∀ n, IsIso (AnodyneHomotopy.anodyneQ.map
      ((twistedHomRowsAugmentation x y).app n)) := by
    rintro ⟨⟨n⟩⟩
    exact (twistedHomRowAugment_isQCatEquivalence x y n).anodyneQ_isIso
  have : IsIso (AnodyneHomotopy.anodyneQ.map
      (SerrePositivity.BisimplicialModel.diagonal.map (twistedHomRowsAugmentation x y))) :=
    SerrePositivity.BisimplicialModel.localized_diagonal_map (twistedHomRowsAugmentation x y) hf
  rw [cosliceTwistedHomMap_eq_diagonal, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp]
  infer_instance

end SerrePositivity.InfinityCategories
