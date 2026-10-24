module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceCommaComparison
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingSpaceModelEquivalence
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftFibrationFiberComparison

/-!
概要：元の coslice の底変換と始点固定 comma の標準比較の同値性。
方針：元の各 fiber の比較を coslice–区間比較と同定し、left fibration の判定を使う。
規約：標的図式を保持した実際の標準射の性質を証明する。
使われ方：局所普遍矢印の始対象性を随伴の comma へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の各標的上の比較は、底変換同型を介した coslice の区間模型への比較。 -/
lemma cosliceCommaComparison_fiber {X Y : SSet.{u}} (G : Y ⟶ X)
    (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    vertexFiberMap (pullback.snd (sliceUnderProjection (SSet.yonedaEquiv.symm x)) G)
        (SerrePositivity.InfinityCategories.F1B.unitCommaFiberProjection G x) (cosliceCommaComparison G x)
        (cosliceCommaComparison_projection G x) y ≫
      (SerrePositivity.InfinityCategories.F1B.unitCommaFiberIntervalIso G x y).hom =
    (cofinalVertexFiberBaseChangeIso (sliceUnderProjection (SSet.yonedaEquiv.symm x)) G y).hom ≫
      cosliceFiberToIntervalMappingSpace x (G.app (Opposite.op ⦋0⦌) y) := by
  apply intervalMappingUncurry_injective
  change intervalMappingUncurry (_ ≫ SerrePositivity.InfinityCategories.F1B.unitCommaFiberToInterval G x y) = _
  rw [intervalMappingUncurry_precomp, SerrePositivity.InfinityCategories.F1B.unitCommaFiberToInterval_uncurry,
    ← unitCommaUncurry_precomp, ← Category.assoc, vertexFiberMap_ι,
    cosliceCommaComparison_uncurry, cosliceFiberToIntervalMappingSpace_uncurry]
  unfold cosliceFiberUncurry
  rw [cofinalVertexFiberBaseChangeIso_hom_ι]

/-- 標準比較は、quasicategory 間の任意の図式の固定始点 comma の全空間の同値。 -/
lemma cosliceCommaComparison_isQCatEquivalence {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (G : Y ⟶ X) (x : X _⦋0⦌) :
    IsQCatEquivalence (cosliceCommaComparison G x) := by
  have : LeftFibration (pullback.snd (sliceUnderProjection (SSet.yonedaEquiv.symm x)) G) :=
    ⟨leftFibrations.pullback_snd _ _ (LeftFibration.mem (p :=
      sliceUnderProjection (SSet.yonedaEquiv.symm x)))⟩
  have : Quasicategory (pullback (sliceUnderProjection (SSet.yonedaEquiv.symm x)) G) :=
    quasicategory_of_innerFibration (pullback.snd _ G)
  have : Quasicategory (unitCommaFiber G x) :=
    quasicategory_of_innerFibration (SerrePositivity.InfinityCategories.F1B.unitCommaFiberProjection G x)
  apply F1B.kanIsQCatEquivalence_of_leftFibration_fibers _ _ _
    (cosliceCommaComparison_projection G x)
  intro y
  have hi := (qCatEquivalenceOfIso (SerrePositivity.InfinityCategories.F1B.unitCommaFiberIntervalIso G x y)).isQCatEquivalence
  apply hi.cancel_right
  change IsQCatEquivalence (_ ≫ (SerrePositivity.InfinityCategories.F1B.unitCommaFiberIntervalIso G x y).hom)
  rw [cosliceCommaComparison_fiber]
  exact (qCatEquivalenceOfIso (cofinalVertexFiberBaseChangeIso
    (sliceUnderProjection (SSet.yonedaEquiv.symm x)) G y)).isQCatEquivalence.comp
      (cosliceFiberToIntervalMappingSpace_isQCatEquivalence x _)

end SerrePositivity.InfinityCategories.HomotopyLimits
