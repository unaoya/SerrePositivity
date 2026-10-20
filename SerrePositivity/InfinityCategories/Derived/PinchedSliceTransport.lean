module
public import SerrePositivity.InfinityCategories.Derived.PinchedFamilyComposition
public import SerrePositivity.InfinityCategories.Derived.RoofRightPrismLift
public import SerrePositivity.InfinityCategories.Core.VertexFiber
/-!
概要：任意の実 pinched Hom 二族から、指定全底を保つ合成候補と実 slice 比較を構成する。
方針：終端固定の right fibration prism を持ち上げ、始点を同じ pinched fiber へ戻す。
規約：有限性を仮定しない。使われ方：評価方程式の実比較への回収。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
/-- 実 pinched Hom の slice 表示の始域は、同じ実始点に厳密に定値。 -/
lemma pinchedFamilySlice_projection {X : SSet.{u}} (x y : X _⦋0⦌) :
    pinchedFamilySlice X x y ≫ sliceOverProjection _ = SSet.const x := by
  dsimp only [pinchedFamilySlice]
  rw [Category.assoc, vertexFiberι_comp, SSet.comp_const]
/-- 任意の二族の輸送で得た実合成係数と、同じ全底を持つ実 slice 比較。 -/
structure PinchedSliceTransportFamily {K X : SSet.{u}} {x y z : X _⦋0⦌}
    (f : K ⟶ pinchedHom x y) (g : K ⟶ pinchedHom y z) where
  coefficient : K ⟶ pinchedHom x z
  homotopy : SSet.Homotopy (coefficient ≫ pinchedFamilySlice X x z)
    (g ≫ pinchedFamilySlice X y z)
  over : homotopy.h ≫ sliceOverProjection _ =
    (intervalFamilyHomotopy (f ≫ pinchedHomToIntervalMappingSpace x y)).h
/-- 任意の quasicategory 標的の二族は、終端固定の同じ実 prism で同時に輸送できる。 -/
lemma pinchedSliceTransportFamily_nonempty {K X : SSet.{u}} [Quasicategory X]
    {x y z : X _⦋0⦌} (f : K ⟶ pinchedHom x y) (g : K ⟶ pinchedHom y z) :
    Nonempty (PinchedSliceTransportFamily f g) := by
  let p := sliceOverProjection (SSet.yonedaEquiv.symm z)
  let β := intervalMappingUncurry (f ≫ pinchedHomToIntervalMappingSpace x y)
  have hβ : (g ≫ pinchedFamilySlice X y z) ≫ p = prismEndpoint 1 K ≫ β := by
    rw [Category.assoc, pinchedFamilySlice_projection, SSet.comp_const]
    exact (intervalFamily_one (f ≫ pinchedHomToIntervalMappingSpace x y)).symm
  obtain ⟨H, hH₁, hHp⟩ := roofRightFibration_lift_end_prism p
    (g ≫ pinchedFamilySlice X y z) β hβ
  let a := prismEndpoint 0 K ≫ H
  have ha : a ≫ p = SSet.const x := by
    change (prismEndpoint 0 K ≫ H) ≫ p = _
    rw [Category.assoc, hHp]
    exact intervalFamily_zero (f ≫ pinchedHomToIntervalMappingSpace x y)
  let v := vertexFiberLift p x a ha
  let c := v ≫ (pinchedHomSliceFiberIso x z).inv
  have hc : c ≫ pinchedFamilySlice X x z = a := by
    dsimp only [c, pinchedFamilySlice]
    rw [Category.assoc, Iso.inv_hom_id_assoc]
    exact vertexFiberLift_ι p x a ha
  let J : SSet.Homotopy (c ≫ pinchedFamilySlice X x z) (g ≫ pinchedFamilySlice X y z) := {
    h := (β_ K (Δ[1] : SSet.{u})).hom ≫ H
    h₀ := by
      change prismEndpoint 0 K ≫ H = c ≫ pinchedFamilySlice X x z
      exact hc.symm
    h₁ := by
      change prismEndpoint 1 K ≫ H = g ≫ pinchedFamilySlice X y z
      exact hH₁
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro s
      exact False.elim s.1.property }
  refine ⟨⟨c, J, ?_⟩⟩
  change ((β_ K (Δ[1] : SSet.{u})).hom ≫ H) ≫ p =
    (β_ K (Δ[1] : SSet.{u})).hom ≫ intervalMappingUncurry
      (f ≫ pinchedHomToIntervalMappingSpace x y)
  rw [Category.assoc, hHp]
end SerrePositivity.InfinityCategories
