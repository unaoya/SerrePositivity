module

public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeEdgeCosliceSection
public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceEdgeFamilyCylinder
public import SerrePositivity.InfinityCategories.HomotopyLimits.HomotopyEndpointTransport

/-!
概要：元の全辺族の底から、同じ終端を普遍相対切断で戻した底への指定円柱。
方針：底の固定終点 fiber の既存の切断比較を包含し、両端だけを厳密に表示変更する。
規約：同じ底の円柱を保持。使われ方：実際の付加辺面と普遍前置の像の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {E B T : SSet.{u}} [Quasicategory B] (e : (Δ[1] : SSet.{u}) ⟶ E)
  (q : E ⟶ B) [InnerFibration q] (a : T ⟶ sliceUnder e) (y : B _⦋0⦌)
  (ha : (a ≫ sliceUnderProjection e) ≫ q = SSet.const y)
local notation "j" => stdSimplex.δ (0 : Fin 2)
local notation "Q" => sliceUnderPostcomp e q
local notation "K" => (a ≫ sliceUnderRestrict e j) ≫ relativeEdgeCosliceSection e q

omit [Quasicategory B] [InnerFibration q] in
include ha in
/-- 底の同じ辺族も、元の固定終点 y 上に留まる。 -/
lemma relativeEdgeFamilyBase_fixed : (a ≫ Q) ≫ sliceUnderProjection (e ≫ q) = SSet.const y := by
  rw [Category.assoc, sliceUnderPostcomp_projection]
  exact ha

/-- 元の底の全辺族を、同じ固定終点の余錐空間で表示する。 -/
def relativeEdgeFamilyBase : T ⟶ coconeMappingSpace (e ≫ q) y :=
  vertexFiberLift (sliceUnderProjection (e ≫ q)) y (a ≫ Q)
    (relativeEdgeFamilyBase_fixed e q a y ha)
local notation "F" => relativeEdgeFamilyBase e q a y ha

omit [Quasicategory B] [InnerFibration q] in
/-- 底の固定終点表示の包含後は、元の全辺族の底そのものである。 -/
lemma relativeEdgeFamilyBase_ι : F ≫ vertexFiberι (sliceUnderProjection (e ≫ q)) y = a ≫ Q :=
  vertexFiberLift_ι _ _ _ _

/-- 底の切断比較の終点は、上の普遍相対切断の像の底と厳密に一致する。 -/
lemma relativeEdgeFamilyBase_section :
    ((F ≫ cosliceRestrictionFiberMap (e ≫ q) j y) ≫ cosliceEdgeSectionFiber (e ≫ q) y) ≫
        vertexFiberι (sliceUnderProjection (e ≫ q)) y = K ≫ Q := by
  rw [Category.assoc (F ≫ cosliceRestrictionFiberMap (e ≫ q) j y),
    cosliceEdgeSectionFiber_ι]
  rw [← Category.assoc (F ≫ cosliceRestrictionFiberMap (e ≫ q) j y),
    Category.assoc F, cosliceRestrictionFiberMap, vertexFiberMap_ι]
  rw [← Category.assoc F, relativeEdgeFamilyBase_ι]
  calc
    _ = (a ≫ (Q ≫ sliceUnderRestrict (e ≫ q) j)) ≫ cosliceEdgeSection (e ≫ q) := by
      simp only [Category.assoc]
    _ = (a ≫ (sliceUnderRestrict e j ≫ sliceUnderPostcomp (j ≫ e) q)) ≫
        cosliceEdgeSection (e ≫ q) :=
      congrArg (fun m ↦ (a ≫ m) ≫ cosliceEdgeSection (e ≫ q))
        (sliceUnderRestrict_postcomp e j q)
    _ = K ≫ Q := by simp only [Category.assoc, relativeEdgeCosliceSection_base]

/-- 元の底の切断比較を保持し、上の普遍相対切断の底へ至る実際の円柱。 -/
def relativeEdgeFamilyBaseCylinder : SSet.Homotopy (a ≫ Q) (K ≫ Q) :=
  homotopyEndpointTransport
    (functorHomotopyPostcomp (cosliceEdgeFamilyCylinder (e ≫ q) y F).homotopy
      (vertexFiberι (sliceUnderProjection (e ≫ q)) y))
    (relativeEdgeFamilyBase_ι e q a y ha) (relativeEdgeFamilyBase_section e q a y ha)

/-- 底の円柱は、元の同じ固定終点の切断比較の raw な包含である。 -/
lemma relativeEdgeFamilyBaseCylinder_raw :
    (relativeEdgeFamilyBaseCylinder e q a y ha).h =
      (cosliceEdgeFamilyCylinder (e ≫ q) y F).homotopy.h ≫
        vertexFiberι (sliceUnderProjection (e ≫ q)) y :=
  homotopyEndpointTransport_raw _ _ _

/-- 底の指定円柱は、元の同じ上の終端係数の底を全時刻固定する。 -/
lemma relativeEdgeFamilyBaseCylinder_target :
    (relativeEdgeFamilyBaseCylinder e q a y ha).h ≫ sliceUnderRestrict (e ≫ q) j =
      fst T Δ[1] ≫ K ≫ sliceUnderRestrict e j ≫ sliceUnderPostcomp (j ≫ e) q := by
  rw [relativeEdgeFamilyBaseCylinder_raw]
  have h := congrArg
    (· ≫ vertexFiberι (sliceUnderProjection (j ≫ (e ≫ q))) y)
    (cosliceEdgeFamilyCylinder (e ≫ q) y F).target
  simp only [Category.assoc, cosliceRestrictionFiberMap, vertexFiberMap_ι] at h
  rw [← Category.assoc F, relativeEdgeFamilyBase_ι] at h
  simp only [Category.assoc] at h
  have hK : K ≫ sliceUnderRestrict e j = a ≫ sliceUnderRestrict e j := by
    rw [Category.assoc, relativeEdgeCosliceSection_target, Category.comp_id]
  rw [← Category.assoc K, hK]
  simpa only [Category.assoc, sliceUnderRestrict_postcomp] using h

end
end SerrePositivity.InfinityCategories.HomotopyLimits
