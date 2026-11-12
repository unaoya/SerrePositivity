module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.CosliceEdgeTrianglePrism
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.IntervalConstantFamily
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.EdgeTransport

/-!
概要：coslice 上の同じ辺の全族から作る実三角形と、その三面。
方針：coslice の展開の普遍性と、左区間比較の元の prism を使う。
規約：頂点ごとの比較に弱めない。使われ方：表現可能値と標準後合成の全族比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open TheSliceAndJoinConstructions MorphismSpaces IsomorphismsAndIsofibrations LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 概要：coslice 上の全区間族を、同じ底の実三角形族として読む。
方針：左に点を置く prism と元の族の coslice 展開を合成する。
規約：元の持ち上げを保持。使われ方：輸送と標準後合成の比較。 -/
def cosliceEdgeTriangleFamily {A X : SSet.{u}} (x : X _⦋0⦌)
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ sliceUnder (SSet.yonedaEquiv.symm x)) :
    A ⊗ (Δ[2] : SSet.{u}) ⟶ X :=
  (β_ A (Δ[2] : SSet.{u})).hom ≫ cosliceEdgeTrianglePrism A ≫ sliceUnderUncurry H

/-- 概要：二つの側面は、同じ coslice 端点の元の区間比較による像。
方針：三角形の面、coslice 展開の自然性、独立した左 prism の式を使う。
規約：端点条件を全パラメータの等式として保持する。
使われ方：輸送の始点と終点の三面の照合。 -/
lemma cosliceEdgeTriangleFamily_side {A X : SSet.{u}} (x y : X _⦋0⦌)
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ sliceUnder (SSet.yonedaEquiv.symm x))
    (i : Fin 2) (f : A ⟶ vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y)
    (h : (stdSimplex.δ i ▷ A) ≫ H = snd (Δ[0] : SSet.{u}) A ≫ f ≫
      vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) :
    (A ◁ stdSimplex.δ i.succ) ≫ cosliceEdgeTriangleFamily x H =
      (intervalFamilyHomotopy (f ≫ cosliceFiberToIntervalMappingSpace x y)).h := by
  have hs : joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.δ i ▷ A) ≫
      sliceUnderUncurry H =
      joinMap (𝟙 (Δ[0] : SSet.{u})) (snd (Δ[0] : SSet.{u}) A) ≫
        sliceUnderUncurry
          (f ≫ vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) := by
    rw [← sliceUnderUncurry_precomp, h, sliceUnderUncurry_precomp]
  unfold cosliceEdgeTriangleFamily
  rw [BraidedCategory.braiding_naturality_right_assoc]
  rw [← Category.assoc (stdSimplex.δ i.succ ▷ A), cosliceEdgeTrianglePrism_side]
  simp only [Category.assoc]
  rw [hs]
  have hp := congrArg (fun k => (β_ A (Δ[1] : SSet.{u})).hom ≫ k ≫
      sliceUnderUncurry
        (f ≫ vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y))
    (coslicePointPrism_eq A)
  simpa only [intervalFamilyHomotopy, cosliceFiberToIntervalMappingSpace_uncurry,
    cosliceFiberUncurry, Category.assoc] using hp

/-- 概要：第二面は coslice 上の元の区間族を底へ送る射そのもの。
方針：prism の第二面と coslice の射影の展開式を使う。
規約：全族の厳密な等式。使われ方：指定辺の定値族への接続。 -/
lemma cosliceEdgeTriangleFamily_edge {A X : SSet.{u}} (x : X _⦋0⦌)
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ sliceUnder (SSet.yonedaEquiv.symm x)) :
    (A ◁ stdSimplex.δ (0 : Fin 3)) ≫ cosliceEdgeTriangleFamily x H =
      (β_ A (Δ[1] : SSet.{u})).hom ≫ H ≫
        sliceUnderProjection (SSet.yonedaEquiv.symm x) := by
  unfold cosliceEdgeTriangleFamily
  rw [BraidedCategory.braiding_naturality_right_assoc]
  rw [← Category.assoc (stdSimplex.δ (0 : Fin 3) ▷ A), cosliceEdgeTrianglePrism_edge]
  rw [sliceUnderUncurry_projection]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
