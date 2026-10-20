module

public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialDiagramHomFamily

/-!
概要：同じ図式の余錐族のホモトピーを、固定終点の初期 Hom の全族へ移す。
方針：初期頂点へ同じ円柱を制限し、全時刻の固定終点条件で fiber に戻す。
規約：元の raw な円柱を保持する。使われ方：左右の根辺比較の初期 Hom への作用。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {K E B T : SSet.{u}} (q : E ⟶ B) (c : E _⦋0⦌)
  (t : K ⟶ E) (v : (Δ[0] : SSet.{u}) ⟶ K) (hv : v ≫ t = SSet.yonedaEquiv.symm c)
  (y : B _⦋0⦌) (a b : T ⟶ sliceUnder t)
  (ha : (a ≫ sliceUnderProjection t) ≫ q = SSet.const y)
  (hb : (b ≫ sliceUnderProjection t) ≫ q = SSet.const y)
  (H : SSet.Homotopy a b)
  (hH : (H.h ≫ sliceUnderProjection t) ≫ q = SSet.const y)
local notation "P" => normalizedCoconeRestriction t v hv
local notation "p" => sliceUnderProjection (SSet.yonedaEquiv.symm c) ≫ q

/-- 元の同じ円柱を、固定終点の初期 Hom の全族の間に持ち上げる。 -/
def initialDiagramHomFamilyHomotopy : SSet.Homotopy
    (initialDiagramHomFamily q c t v hv y a ha) (initialDiagramHomFamily q c t v hv y b hb) where
  h := vertexFiberLift p y (H.h ≫ P) (by
    calc
      _ = (H.h ≫ sliceUnderProjection t) ≫ q := by
        rw [← Category.assoc (H.h ≫ P) (sliceUnderProjection (SSet.yonedaEquiv.symm c)) q,
          Category.assoc H.h P, normalizedCoconeRestriction_projection]
      _ = _ := hH)
  h₀ := by
    change SSet.ι₀ ≫ vertexFiberLift p y (H.h ≫ P) _ =
      initialDiagramHomFamily q c t v hv y a ha
    apply vertexFiber_hom_ext p y
    rw [Category.assoc, vertexFiberLift_ι, ← Category.assoc, H.h₀,
      initialDiagramHomFamily, vertexFiberLift_ι]
  h₁ := by
    change SSet.ι₁ ≫ vertexFiberLift p y (H.h ≫ P) _ =
      initialDiagramHomFamily q c t v hv y b hb
    apply vertexFiber_hom_ext p y
    rw [Category.assoc, vertexFiberLift_ι, ← Category.assoc, H.h₁,
      initialDiagramHomFamily, vertexFiberLift_ι]
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 初期 Hom 空間の包含後は、元の円柱の同じ頂点制限である。 -/
lemma initialDiagramHomFamilyHomotopy_ι :
    (initialDiagramHomFamilyHomotopy q c t v hv y a b ha hb H hH).h ≫ vertexFiberι p y =
      H.h ≫ P := by
  rw [initialDiagramHomFamilyHomotopy, vertexFiberLift_ι]

/-- 同じ円柱の可変終点評価も、元の円柱の全族そのもの。 -/
lemma initialDiagramHomFamilyHomotopy_evaluation :
    (initialDiagramHomFamilyHomotopy q c t v hv y a b ha hb H hH).h ≫
        leftFibrationInitialEvaluation q c y =
      vertexFiberLift q y (H.h ≫ sliceUnderProjection t) hH := by
  apply vertexFiber_hom_ext q y
  rw [Category.assoc, leftFibrationInitialEvaluation, vertexFiberMap_ι,
    ← Category.assoc, initialDiagramHomFamilyHomotopy_ι, vertexFiberLift_ι,
    Category.assoc, normalizedCoconeRestriction_projection]

/-- 底の初期 Hom への像は、元の円柱の底の同じ初期頂点への制限。 -/
lemma initialDiagramHomFamilyHomotopy_base :
    (initialDiagramHomFamilyHomotopy q c t v hv y a b ha hb H hH).h ≫
        leftFibrationInitialProjection q c y ≫
          vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm c ≫ q)) y =
      (H.h ≫ sliceUnderPostcomp t q) ≫ normalizedCoconeRestriction (t ≫ q) v
        (by rw [← Category.assoc, hv]) := by
  rw [leftFibrationInitialProjection, vertexFiberMap_ι, ← Category.assoc,
    initialDiagramHomFamilyHomotopy_ι]
  exact normalizedCoconeRestriction_postcomp_family t v _ hv q H.h

end
end SerrePositivity.InfinityCategories.HomotopyLimits
