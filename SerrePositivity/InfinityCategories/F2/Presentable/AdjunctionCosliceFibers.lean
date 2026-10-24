module

public import SerrePositivity.InfinityCategories.F2.Presentable.AdjunctionCosliceComparison
public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitCommaFiberIntervalIso

/-!
概要：固定始点の全比較の fiber を元の区間写像空間比較と同定する。
方針：普遍 coslice の区間表示と矢印比較のパラメータ自然性を使う。
規約：全比較とその各点への制限の両方を保持する。
使われ方：随伴の Hom 族の分類比較の可逆性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：coslice の指定 fiber の矢印族は元の区間比較へ渡す族と一致する。
方針：両端と普遍族の raw なホモトピーを比較する。
規約：標的の quasicategory 性を要求しない。
使われ方：全比較の fiber の厳密な計算。 -/
lemma cosliceMappingArrow_fiber {X Y : SSet.{u}} (F : X ⟶ Y)
    (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    vertexFiberι (sliceUnderProjection
      (SSet.yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x))) y ≫
        cosliceMappingArrow F x =
      leftMappingIntervalFamily F x y (cosliceFiberToIntervalMappingSpace _ y) := by
  apply leftMappingArrow_hom_ext
  · rw [Category.assoc]
    change _ ≫ (leftMappingArrowLift _ _ _ _ ≫ _) = _
    rw [leftMappingArrowLift_source, SSet.comp_const, leftMappingIntervalFamily_source]
  · rw [Category.assoc]
    change _ ≫ (leftMappingArrowLift _ _ _ _ ≫ _) = _
    rw [leftMappingArrowLift_target, vertexFiberι_comp, leftMappingIntervalFamily_target]
  · rw [leftMappingArrowHomotopy_precomp_h, leftMappingIntervalFamily_h]
    change _ ≫ (leftMappingArrowHomotopy (leftMappingArrowLift _ _ _ _)).h = _
    rw [leftMappingArrowLift_homotopy_h]
    change _ ≫ (β_ _ (Δ[1] : SSet.{u})).hom ≫ leftMappingSpacePrism _ ≫
      sliceUnderUncurry (𝟙 _) =
        (β_ _ (Δ[1] : SSet.{u})).hom ≫
          intervalMappingUncurry (cosliceFiberToIntervalMappingSpace _ y)
    have hu := cosliceFiberToIntervalMappingSpace_uncurry
      (𝟙 (vertexFiber (sliceUnderProjection
        (SSet.yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x))) y))
    simp only [Category.id_comp] at hu
    rw [hu]
    unfold cosliceFiberUncurry
    rw [← Category.assoc, ← Category.assoc,
      BraidedCategory.braiding_naturality_left,
      Category.assoc, Category.assoc]
    rw [← Category.assoc (Δ[1] ◁ vertexFiberι _ y) (leftMappingSpacePrism _) _,
      leftMappingSpacePrism_naturality, Category.assoc]
    rw [← sliceUnderUncurry_precomp, Category.comp_id, Category.id_comp]

/-- 概要：全比較の指定 fiber は同じ元の区間比較で表される。
方針：comma の包含と区間の uncurry を計算し、普遍矢印族の一致を使う。
規約：元の比較 q の作用そのものの等式。
使われ方：随伴の全 Hom 比較の各点での可逆性。 -/
lemma adjunctionCosliceComparison_fiber {X Y : SSet.{u}}
    {F : X ⟶ Y} {G : Y ⟶ X} (q : MappingArrowComparison F G)
    (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    vertexFiberMap (sliceUnderProjection
      (SSet.yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x)))
        (F1B.unitCommaFiberProjection G x) (adjunctionCosliceComparison q x)
        (adjunctionCosliceComparison_projection q x) y ≫
          F1B.unitCommaFiberToInterval G x y =
      cosliceFiberToIntervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y ≫ q.intervalMap x y := by
  apply intervalMappingUncurry_injective
  rw [intervalMappingUncurry_precomp, F1B.unitCommaFiberToInterval_uncurry,
    ← unitCommaUncurry_precomp, ← Category.assoc, vertexFiberMap_ι]
  unfold adjunctionCosliceComparison
  rw [Category.assoc, vertexFiberLift_ι, ← Category.assoc, cosliceMappingArrow_fiber]
  have h := q.intervalMap_family_h x y (cosliceFiberToIntervalMappingSpace _ y)
  apply (cancel_epi (β_ _ (Δ[1] : SSet.{u})).hom).mp
  exact h.symm

end SerrePositivity.InfinityCategories.F2.Presentable
