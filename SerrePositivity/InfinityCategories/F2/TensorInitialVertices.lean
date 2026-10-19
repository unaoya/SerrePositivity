module

public import SerrePositivity.InfinityCategories.F2.PinchedHomTensorIso
public import SerrePositivity.InfinityCategories.F2.QCatTensorAndArrowObjects
public import SerrePositivity.InfinityCategories.F1B.KanRelativeInitialBoundaryCriterion
public import SerrePositivity.KST.SConstruction.ContractibleKanProducts

/-!
概要：二つの始対象の組は直積の始対象。
方針：右写像空間を二つの可縮空間の直積として表示する。
規約：元の二つの頂点をそのまま組にする。
使われ方：lax pullback の二入力と両端の始対象の判定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：二つの始対象の組は直積の始対象。
方針：各因子への写像空間の可縮性を直積同型で戻す。
規約：直積の quasicategory 性は既存の充填性から得る。
使われ方：lax pullback の成分ごとの始対象。 -/
lemma isInitialVertex_tensor {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (x : X _⦋0⦌) (y : Y _⦋0⦌) (hx : IsInitialVertex x) (hy : IsInitialVertex y) :
    IsInitialVertex (X := X ⊗ Y) (x, y) := by
  have : Quasicategory (X ⊗ Y) := quasicategory_tensor X Y
  apply F1B.kanIsInitialVertex_of_pinchedHom_isContractibleKan
  intro z
  exact isContractibleKan_of_iso (pinchedHomTensorIso (x, y) z).symm
    (SerrePositivity.KST.SConstruction.contractibleKan_tensor
      (F1B.kanInitialVertex_pinchedHom_isContractibleKan hx _)
      (F1B.kanInitialVertex_pinchedHom_isContractibleKan hy _))

end SerrePositivity.InfinityCategories.F2
