module

public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeEdgeFamilyBaseCylinder
public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeCosliceSpecifiedHomotopy

/-!
概要：実際の全辺族から、その終端を普遍相対切断で戻した全族へ指定底上で結ぶ。
方針：元の底の切断比較を相対 coslice に持ち上げ、終端係数を全時刻固定する。
規約：底は同じ元の円柱の raw な包含。使われ方：枝の前置像と根辺初期族の比較。
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
local notation "K" => (a ≫ sliceUnderRestrict e j) ≫ relativeEdgeCosliceSection e q

/-- 元の全辺族と普遍前置像の間に、同じ底の円柱と終端固定を保つ持ち上げがある。 -/
lemma exists_relativeEdgeFamilyRetraction :
    ∃ H : SSet.Homotopy a K,
      H.h ≫ sliceUnderRestrict e j = fst T Δ[1] ≫ K ≫ sliceUnderRestrict e j ∧
      H.h ≫ sliceUnderPostcomp e q = (relativeEdgeFamilyBaseCylinder e q a y ha).h := by
  apply exists_relativeCosliceSpecifiedHomotopy e q j endpointInclusion_rightAnodyne a K
    (by simp only [Category.assoc, relativeEdgeCosliceSection_target, Category.comp_id])
    (relativeEdgeFamilyBaseCylinder e q a y ha)
    (relativeEdgeFamilyBaseCylinder_target e q a y ha)

/-- 同じ底の切断比較の上で、元の全辺族を普遍相対切断の像へ結ぶ。 -/
def relativeEdgeFamilyRetraction : SSet.Homotopy a K :=
  (exists_relativeEdgeFamilyRetraction e q a y ha).choose

/-- 比較は、元の同じ終端係数を全時刻固定する。 -/
lemma relativeEdgeFamilyRetraction_target :
    (relativeEdgeFamilyRetraction e q a y ha).h ≫ sliceUnderRestrict e j =
      fst T Δ[1] ≫ a ≫ sliceUnderRestrict e j := by
  rw [relativeEdgeFamilyRetraction]
  simpa only [Category.assoc, relativeEdgeCosliceSection_target, Category.comp_id] using
    (exists_relativeEdgeFamilyRetraction e q a y ha).choose_spec.1

/-- 比較の底は、元の同じ切断比較の raw な円柱である。 -/
lemma relativeEdgeFamilyRetraction_base :
    (relativeEdgeFamilyRetraction e q a y ha).h ≫ sliceUnderPostcomp e q =
      (cosliceEdgeFamilyCylinder (e ≫ q) y (relativeEdgeFamilyBase e q a y ha)).homotopy.h ≫
        vertexFiberι (sliceUnderProjection (e ≫ q)) y :=
  (exists_relativeEdgeFamilyRetraction e q a y ha).choose_spec.2.trans
    (relativeEdgeFamilyBaseCylinder_raw e q a y ha)

/-- 比較の可変終点は、元の同じ全族の終点を全時刻固定する。 -/
lemma relativeEdgeFamilyRetraction_projection :
    (relativeEdgeFamilyRetraction e q a y ha).h ≫ sliceUnderProjection e =
      fst T Δ[1] ≫ a ≫ sliceUnderProjection e := by
  rw [← sliceUnderRestrict_projection e j,
    ← Category.assoc (relativeEdgeFamilyRetraction e q a y ha).h,
    relativeEdgeFamilyRetraction_target]
  simp only [Category.assoc]

/-- 元の固定終点 y の条件も、比較の全時刻で保たれる。 -/
lemma relativeEdgeFamilyRetraction_fixed :
    ((relativeEdgeFamilyRetraction e q a y ha).h ≫ sliceUnderProjection e) ≫ q =
      SSet.const y := by
  rw [relativeEdgeFamilyRetraction_projection]
  simpa only [Category.assoc, ha] using (SSet.comp_const (fst T Δ[1]) y)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
