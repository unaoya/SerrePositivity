module
public import SerrePositivity.EInfinity.HomotopyWeight.BousfieldKanSkeletonPushout
public import SerrePositivity.EInfinity.HomotopyWeight.BousfieldKanCellLifting
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
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits Opposite SSet
open SerrePositivity.DiagramModel.SimplicialDiagramSkeleton
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

/-- 同じBK重みの第零骨格は、全図式圏の始対象。 -/
def bkSkeletonZeroIsInitial : IsInitial ((bkSkeleton I).obj 0) :=
  Functor.isInitial (fun i =>
    (Subcomplex.isInitialBot (X := (bousfieldKanWeight I).obj i)).ofIso
      (Subcomplex.eqToIso (((bousfieldKanWeight I).obj i).skeleton_zero)).symm)

/-- 同じ連続する骨格の射は、自由境界の右類に対して左持ち上げ性を持つ。 -/
theorem bkSkeleton_step_llp (n : ℕ) :
    (boundaries I).rlp.llp ((bkSkeleton I).map (homOfLE (Nat.le_succ n))) :=
  MorphismProperty.of_isPushout (bkCellAttachment_isPushout I n)
    (bkCellTensor_map_llp I n ∂Δ[n].ι (MorphismProperty.ofHoms.mk n))

/-- 元の始対象からBK重みへの射を、同じ自由境界による逐次合成として読む。 -/
def bkSkeletonTransfinite :
    (boundaries I).rlp.llp.TransfiniteCompositionOfShape ℕ (initial.to (bousfieldKanWeight I)) where
  F := bkSkeleton I
  isoBot := (bkSkeletonZeroIsInitial I).uniqueUpToIso initialIsInitial
  incl := (skeletonCocone I (bousfieldKanWeight I)).ι
  isColimit := skeletonCoconeIsColimit I (bousfieldKanWeight I)
  fac := initialIsInitial.hom_ext _ _
  map_mem n hn := bkSkeleton_step_llp I n

/-- 元のBK重みそのものは、自由境界生成族に関して射影cofibrant。 -/
theorem bousfieldKanWeight_cofibrant :
    (boundaries I).rlp.llp (initial.to (bousfieldKanWeight I)) :=
  MorphismProperty.transfiniteCompositionsOfShape_le _ ℕ _ ⟨bkSkeletonTransfinite I⟩

end SerrePositivity.EInfinity.HomotopyWeight
