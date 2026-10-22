module
public import SerrePositivity.KST.Fibration.PointSourceCosliceFixedHomotopy
public import SerrePositivity.InfinityCategories.F1.LeftIntervalFatNaturality
public import SerrePositivity.InfinityCategories.Core.FatJoinComparisonNaturality

/-! # 同じ全 coslice 比較の指定終点 fiber への制限と元の区間評価との照合 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {A X P : SSet.{u}} {x y : X _⦋0⦌} {g : A ⟶ X}
  {F : fatJoin (Δ[0] : SSet.{u}) A ⟶ X} (d : PointSourceCosliceData x g F)
  (i : P ⟶ A) (hy : i ≫ g = SSet.const y)

/-- 元の全 coslice 関手を、同じ指定終点の部分族上で厳密な fiber へ制限する。 -/
def PointSourceCosliceData.toFiber :
    P ⟶ vertexFiber (sliceUnderProjection (yonedaEquiv.symm x)) y :=
  vertexFiberLift _ _ (i ≫ d.toCoslice) (by
    rw [Category.assoc, d.toCoslice_projection, hy])

/-- 同じ fiber 内の族を展開すると、元の cone の同じ部分族への制限を回収する。 -/
theorem PointSourceCosliceData.toFiber_uncurry :
    cosliceFiberUncurry (d.toFiber i hy) = joinMap (𝟙 (Δ[0] : SSet.{u})) i ≫ d.cone := by
  rw [cosliceFiberUncurry, PointSourceCosliceData.toFiber, vertexFiberLift_ι,
    sliceUnderUncurry_precomp, PointSourceCosliceData.toCoslice, sliceUnderUncurry_curry]

/-- 全族の同じ比較ホモトピーを、指定された元の部分族へ制限する。 -/
def PointSourceCosliceData.fiberFatHomotopy :
    SSet.Homotopy
      (fatJoinMap (𝟙 (Δ[0] : SSet.{u})) i ≫ (fatJoinComparison Δ[0] A ≫ d.cone))
      (fatJoinMap (𝟙 (Δ[0] : SSet.{u})) i ≫ F) :=
  stableHomotopyPrecomp _ d.homotopy

/-- 元の部分族で、coslice fiber の区間比較と指定された実評価を同じホモトピーで結ぶ。 -/
def PointSourceCosliceData.toFiberIntervalHomotopy
    (a : P ⟶ intervalMappingSpace x y)
    (ha : leftIntervalFatPrism P ≫ (fatJoinMap (𝟙 (Δ[0] : SSet.{u})) i ≫ F) =
      intervalMappingUncurry a) :
    SSet.Homotopy (d.toFiber i hy ≫ cosliceFiberToIntervalMappingSpace x y) a := by
  apply intervalMappingHomotopyOfLeftFatJoin (d.fiberFatHomotopy i)
    (d.toFiber i hy ≫ cosliceFiberToIntervalMappingSpace x y) a ?_ ha ?_ ?_
  · rw [← Category.assoc (fatJoinMap _ _), fatJoinComparison_naturality,
      Category.assoc, ← d.toFiber_uncurry i hy, ← Category.assoc,
      leftIntervalFatPrism_comparison]
    exact (cosliceFiberToIntervalMappingSpace_uncurry _).symm
  · change (fatJoinInl Δ[0] P ▷ (Δ[1] : SSet.{u})) ≫
      (fatJoinMap (𝟙 (Δ[0] : SSet.{u})) i ▷ Δ[1]) ≫ d.homotopy.h = _
    rw [← comp_whiskerRight_assoc, fatJoinInl_map, Category.id_comp, d.fixed_left]
  · change (fatJoinInr Δ[0] P ▷ (Δ[1] : SSet.{u})) ≫
      (fatJoinMap (𝟙 (Δ[0] : SSet.{u})) i ▷ Δ[1]) ≫ d.homotopy.h = _
    rw [← comp_whiskerRight_assoc, fatJoinInr_map, comp_whiskerRight_assoc,
      d.fixed_right, ← Category.assoc, whiskerRight_fst, Category.assoc, hy]

end SerrePositivity.KST.Fibration
