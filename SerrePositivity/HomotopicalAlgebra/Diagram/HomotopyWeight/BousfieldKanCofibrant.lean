module
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.BousfieldKanSkeletonPushout
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.BousfieldKanCellLifting
public import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Terminal

/-!
概要：元のBK重みは、自由境界生成族に関して射影cofibrant。
方針：同じ骨格の押し出しと逐次余極限を、既存の左持ち上げ性の安定性へ渡す。
規約：IS-W2 R03aの細胞分解の証明分割。SSetモデル構造を仮定しない。
使われ方：指定された一点重みへの同じ比較射を選ぶ。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.SSet
open _root_.SerrePositivity.DiagramModel.SimplicialDiagramSkeleton
open _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped _root_.Simplicial
variable (I : Type u) [SmallCategory I]

/-- 同じBK重みの第零骨格は、全図式圏の始対象。 -/
def bkSkeletonZeroIsInitial : IsInitial ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkSkeleton I).obj 0) :=
  Functor.isInitial (fun i =>
    (Subcomplex.isInitialBot (X := (bousfieldKanWeight I).obj i)).ofIso
      (Subcomplex.eqToIso (((bousfieldKanWeight I).obj i).skeleton_zero)).symm)

/-- 同じ連続する骨格の射は、自由境界の右類に対して左持ち上げ性を持つ。 -/
theorem bkSkeleton_step_llp (n : ℕ) :
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries I).rlp.llp ((_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkSkeleton I).map (homOfLE (Nat.le_succ n))) :=
  MorphismProperty.of_isPushout (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellAttachment_isPushout I n)
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkCellTensor_map_llp I n ∂Δ[n].ι (MorphismProperty.ofHoms.mk n))

/-- 元の始対象からBK重みへの射を、同じ自由境界による逐次合成として読む。 -/
def bkSkeletonTransfinite :
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries I).rlp.llp.TransfiniteCompositionOfShape ℕ (initial.to (bousfieldKanWeight I)) where
  F := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkSkeleton I
  isoBot := (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkSkeletonZeroIsInitial I).uniqueUpToIso initialIsInitial
  incl := (skeletonCocone I (bousfieldKanWeight I)).ι
  isColimit := skeletonCoconeIsColimit I (bousfieldKanWeight I)
  fac := initialIsInitial.hom_ext _ _
  map_mem n hn := _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkSkeleton_step_llp I n

/-- 元のBK重みそのものは、自由境界生成族に関して射影cofibrant。 -/
theorem bousfieldKanWeight_cofibrant :
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.boundaries I).rlp.llp (initial.to (bousfieldKanWeight I)) :=
  MorphismProperty.transfiniteCompositionsOfShape_le _ ℕ _ ⟨_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkSkeletonTransfinite I⟩

end SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight
