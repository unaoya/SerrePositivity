module

public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialHomEdgeNaturality

/-!
概要：始対象を含む任意の図式の余錐族を、図式全体を保った Hom 比較の中間空間へ移す。
方針：指定始点への制限を fiber に戻し、始対象の評価上で同じ終点を持つ二族を結ぶ。
規約：形状やパラメータの Kan 性は不要。底の射の充填性も要求しない。
使われ方：右修正四面体の全 Hom の族を、共通部分の始対象の Hom 比較へ移す。
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
  (y : B _⦋0⦌) (a : T ⟶ sliceUnder t)
  (ha : (a ≫ sliceUnderProjection t) ≫ q = SSet.const y)

/-- 図式全体の族を指定した始点へ制限し、同じ可変終点の中間 Hom 空間へ戻す。 -/
def initialDiagramHomFamily : T ⟶ leftFibrationInitialTotal q c y :=
  vertexFiberLift (sliceUnderProjection (SSet.yonedaEquiv.symm c) ≫ q) y
    (a ≫ normalizedCoconeRestriction t v hv) (by
      rw [← Category.assoc, Category.assoc a, normalizedCoconeRestriction_projection, ha])

/-- 始点へ制限しても、可変終点の fiber の族を厳密に保つ。 -/
lemma initialDiagramHomFamily_evaluation :
    initialDiagramHomFamily q c t v hv y a ha ≫ leftFibrationInitialEvaluation q c y =
      vertexFiberLift q y (a ≫ sliceUnderProjection t) ha := by
  apply vertexFiber_hom_ext q y
  rw [Category.assoc, leftFibrationInitialEvaluation, vertexFiberMap_ι,
    ← Category.assoc, initialDiagramHomFamily, vertexFiberLift_ι, vertexFiberLift_ι,
    Category.assoc, normalizedCoconeRestriction_projection]

/-- 図式を保つ中間 Hom の族の底は、底の図式の同じ始点への制限そのもの。 -/
lemma initialDiagramHomFamily_base :
    initialDiagramHomFamily q c t v hv y a ha ≫ leftFibrationInitialProjection q c y ≫
        vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm c ≫ q)) y =
      (a ≫ sliceUnderPostcomp t q) ≫ normalizedCoconeRestriction (t ≫ q) v
        (by rw [← Category.assoc, hv]) := by
  rw [leftFibrationInitialProjection, vertexFiberMap_ι, ← Category.assoc,
    initialDiagramHomFamily, vertexFiberLift_ι]
  exact normalizedCoconeRestriction_postcomp_family t v _ hv q a

/-- 図式を保持した中間 Hom の族と選んだ始対象の切断を、終点を保つ一つのホモトピーで結ぶ。 -/
lemma initialDiagramHomFamily_section_homotopy (hc : IsInitialVertex c) :
    ∃ H : SSet.Homotopy
      (vertexFiberLift q y (a ≫ sliceUnderProjection t) ha ≫ leftFibrationInitialSection q c hc y)
      (initialDiagramHomFamily q c t v hv y a ha),
      H.h ≫ leftFibrationInitialEvaluation q c y =
        fst T (Δ[1] : SSet.{u}) ≫ vertexFiberLift q y (a ≫ sliceUnderProjection t) ha := by
  have := leftFibrationInitialEvaluation_trivialKanFibration q c hc y
  obtain ⟨H, hH⟩ := exists_homotopy_over_trivialKanFibration (leftFibrationInitialEvaluation q c y)
    (vertexFiberLift q y (a ≫ sliceUnderProjection t) ha ≫ leftFibrationInitialSection q c hc y)
    (initialDiagramHomFamily q c t v hv y a ha)
    (by rw [Category.assoc, leftFibrationInitialSection_evaluation, Category.comp_id,
      initialDiagramHomFamily_evaluation])
  refine ⟨H, ?_⟩
  simpa only [Category.assoc, initialDiagramHomFamily_evaluation] using hH

/-- 同じ図式の全パラメータ族が定める実際の Hom は、元の始対象の Hom 比較とホモトピック。 -/
lemma initialDiagramHomComparison_homotopy (hc : IsInitialVertex c) :
    Nonempty (SSet.Homotopy
      (vertexFiberLift q y (a ≫ sliceUnderProjection t) ha ≫
        leftFibrationInitialHomComparison q c hc y)
      (initialDiagramHomFamily q c t v hv y a ha ≫ leftFibrationInitialProjection q c y ≫
        (leftFibrationInitialBaseIso q c y).hom)) := by
  obtain ⟨H, _⟩ := initialDiagramHomFamily_section_homotopy q c t v hv y a ha hc
  exact ⟨by simpa only [Category.assoc, leftFibrationInitialHomComparison] using
    (functorHomotopyPostcomp H
      (leftFibrationInitialProjection q c y ≫ (leftFibrationInitialBaseIso q c y).hom))⟩

end
end SerrePositivity.InfinityCategories.HomotopyLimits
