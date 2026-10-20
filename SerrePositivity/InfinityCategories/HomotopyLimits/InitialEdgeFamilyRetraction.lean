module

public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeEdgeFamilyRetraction
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialDiagramHomotopyConstant

/-!
概要：実際の辺面の全族から普遍前置の像への比較を、同じ初期 Hom 空間へ移す。
方針：指定した底の切断比較を持つ全辺円柱を、その始点へ厳密に制限する。
規約：評価固定と底の元の raw な比較を保持。使われ方：枝終点と根辺初期族の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {E B T : SSet.{u}} [Quasicategory B] (q : E ⟶ B) [InnerFibration q]
  (c : E _⦋0⦌) (e : (Δ[1] : SSet.{u}) ⟶ E)
  (he : stdSimplex.δ (1 : Fin 2) ≫ e = SSet.yonedaEquiv.symm c)
  (y : B _⦋0⦌) (a : T ⟶ sliceUnder e)
  (ha : (a ≫ sliceUnderProjection e) ≫ q = SSet.const y)
local notation "j" => stdSimplex.δ (0 : Fin 2)
local notation "K" => (a ≫ sliceUnderRestrict e j) ≫ relativeEdgeCosliceSection e q
local notation "H" => relativeEdgeFamilyRetraction e q a y ha

include ha in
/-- 同じ終端を相対切断で戻した族も、元の固定終点 y 上にある。 -/
lemma initialEdgeFamilyRetraction_section_fixed :
    (K ≫ sliceUnderProjection e) ≫ q = SSet.const y := by
  rw [Category.assoc (a ≫ sliceUnderRestrict e j), relativeEdgeCosliceSection_projection]
  rw [Category.assoc a, sliceUnderRestrict_projection]
  exact ha
local notation "hK" => initialEdgeFamilyRetraction_section_fixed q e y a ha

/-- 同じ元の辺面の初期族から、同じ終端を普遍前置した族への初期 Hom 円柱。 -/
def initialEdgeFamilyRetraction : SSet.Homotopy
    (initialDiagramHomFamily q c e (stdSimplex.δ (1 : Fin 2)) he y a ha)
    (initialDiagramHomFamily q c e (stdSimplex.δ (1 : Fin 2)) he y K hK) :=
  initialDiagramHomFamilyHomotopy q c e (stdSimplex.δ (1 : Fin 2)) he y a K ha hK H
    (relativeEdgeFamilyRetraction_fixed e q a y ha)
local notation "I" => initialEdgeFamilyRetraction q c e he y a ha

/-- 初期 Hom の包含後は、指定した同じ全辺円柱の始点制限である。 -/
lemma initialEdgeFamilyRetraction_ι :
    (I).h ≫ vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm c) ≫ q) y =
      (H).h ≫ normalizedCoconeRestriction e (stdSimplex.δ (1 : Fin 2)) he :=
  initialDiagramHomFamilyHomotopy_ι _ _ _ _ _ _ _ _ _ _ _ _

/-- 比較の全時刻で、元の全族と同じ可変終点を評価する。 -/
lemma initialEdgeFamilyRetraction_evaluation :
    (I).h ≫ leftFibrationInitialEvaluation q c y =
      fst T Δ[1] ≫ vertexFiberLift q y (a ≫ sliceUnderProjection e) ha := by
  apply vertexFiber_hom_ext q y
  rw [Category.assoc, leftFibrationInitialEvaluation, vertexFiberMap_ι, ← Category.assoc,
    initialEdgeFamilyRetraction_ι, Category.assoc, normalizedCoconeRestriction_projection,
    relativeEdgeFamilyRetraction_projection, Category.assoc, vertexFiberLift_ι]

/-- 底の包含後は、元の底の同じ切断比較円柱の始点制限そのもの。 -/
lemma initialEdgeFamilyRetraction_base :
    (I).h ≫ leftFibrationInitialProjection q c y ≫
        vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm c ≫ q)) y =
      ((cosliceEdgeFamilyCylinder (e ≫ q) y
        (relativeEdgeFamilyBase e q a y ha)).homotopy.h ≫
          vertexFiberι (sliceUnderProjection (e ≫ q)) y) ≫
            normalizedCoconeRestriction (e ≫ q) (stdSimplex.δ (1 : Fin 2))
              ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ q) he)) := by
  rw [initialEdgeFamilyRetraction, initialDiagramHomFamilyHomotopy_base,
    relativeEdgeFamilyRetraction_base]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
