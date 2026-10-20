module

public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialDiagramHomotopy

/-!
概要：初期 Hom へ移した同じ円柱の、底と可変終点の全時刻固定を回収する。
方針：fiber 包含後の raw な式を使い、元の定値円柱の等式を制限する。
規約：両端の一致だけで定値とはしない。使われ方：左右の初期 Hom 比較の合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {K E B T : SSet.{u}} (q : E ⟶ B) (c : E _⦋0⦌)
  (t : K ⟶ E) (v : (Δ[0] : SSet.{u}) ⟶ K) (hv : v ≫ t = SSet.yonedaEquiv.symm c)
  (y : B _⦋0⦌) (a b : T ⟶ sliceUnder t)
  (ha : (a ≫ sliceUnderProjection t) ≫ q = SSet.const y)
  (hb : (b ≫ sliceUnderProjection t) ≫ q = SSet.const y)
  (H : SSet.Homotopy a b) (hH : (H.h ≫ sliceUnderProjection t) ≫ q = SSet.const y)
local notation "G" => initialDiagramHomFamilyHomotopy q c t v hv y a b ha hb H hH
local notation "I" => initialDiagramHomFamily q c t v hv y b hb

/-- 元の円柱が可変終点の全族を固定すれば、初期 Hom での評価も全時刻固定する。 -/
lemma initialDiagramHomFamilyHomotopy_evaluation_constant
    (he : H.h ≫ sliceUnderProjection t = fst T Δ[1] ≫ b ≫ sliceUnderProjection t) :
    (G).h ≫ leftFibrationInitialEvaluation q c y =
      fst T Δ[1] ≫ I ≫ leftFibrationInitialEvaluation q c y := by
  apply vertexFiber_hom_ext q y
  simp only [Category.assoc, leftFibrationInitialEvaluation, vertexFiberMap_ι]
  rw [← Category.assoc, initialDiagramHomFamilyHomotopy_ι,
    Category.assoc, normalizedCoconeRestriction_projection, he]
  have hI := congrArg (fun m ↦ m ≫ vertexFiberι q y)
    (initialDiagramHomFamily_evaluation q c t v hv y b hb)
  simp only [Category.assoc, leftFibrationInitialEvaluation, vertexFiberMap_ι,
    vertexFiberLift_ι] at hI
  simpa only [Category.assoc] using (congrArg (fun m ↦ fst T (Δ[1] : SSet.{u}) ≫ m) hI).symm

/-- 元の底の円柱の全時刻固定は、初期 Hom の底への射影でも厳密に保たれる。 -/
lemma initialDiagramHomFamilyHomotopy_base_constant
    (hp : H.h ≫ sliceUnderPostcomp t q = fst T Δ[1] ≫ b ≫ sliceUnderPostcomp t q) :
    (G).h ≫ leftFibrationInitialProjection q c y =
      fst T Δ[1] ≫ I ≫ leftFibrationInitialProjection q c y := by
  apply vertexFiber_hom_ext (sliceUnderProjection (SSet.yonedaEquiv.symm c ≫ q)) y
  have h := initialDiagramHomFamilyHomotopy_base q c t v hv y a b ha hb H hH
  rw [hp] at h
  have hI := congrArg (fun m ↦ fst T (Δ[1] : SSet.{u}) ≫ m)
    (initialDiagramHomFamily_base q c t v hv y b hb)
  simpa only [Category.assoc] using h.trans hI.symm

end SerrePositivity.InfinityCategories.HomotopyLimits
