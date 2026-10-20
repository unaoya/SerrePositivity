module
public import SerrePositivity.InfinityCategories.Derived.RoofPointBoundaryHorn
public import SerrePositivity.InfinityCategories.Derived.DGLastHornGeneralRefinementFaces

/-! # 一般閉細分ホーンの充填からの実 over 単体

概要：実 over 境界から作ったホーンの閉始点細分の充填を、終点固定の実 over 単体へ戻す。
方針：元の零面の厳密保存と、全次元の join による逆回収を接続する。
規約：元の境界零面を保持する。使われ方：一般有限図式の高次錐の実単体。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {n : ℕ}
variable (a : Δ[0] ⟶ dgNerve A D) (B : (∂Δ[n + 1] : SSet.{max u v}) ⟶ sliceOver a)
variable (q : D) (s : ForgetEnrichment.of (Complex A) q ⟶
  ForgetEnrichment.of (Complex A) ((HornData.knownData (roofPointBoundaryHorn a B)).obj 0))
variable (F : Δ[n + 2] ⟶ dgNerve A D)
variable (hF : (horn (n + 2) (Fin.last (n + 2))).ι ≫ F =
  dgGeneralLastHornSourceRefinement (roofPointBoundaryHorn a B) q s)

include hF

/-- 細分ホーンの実充填の零面は、元の同じ over 境界零面の回収単体。 -/
lemma dgOverBoundaryRefinedFiller_face_zero :
    SSet.stdSimplex.δ (0 : Fin (n + 3)) ≫ F =
      roofPointSliceSimplex a (SSet.yonedaEquiv (boundary.ι (0 : Fin (n + 2)) ≫ B)) := by
  rw [← horn.ι_ι_assoc (Fin.last (n + 2)) 0 (by simp), hF,
    dgGeneralLastHornSourceRefinement_preserves_face_zero]
  exact roofPointBoundaryHorn_face a B 0

/-- 同じ実充填から戻る、元の終点を固定した実 over 単体。 -/
def dgOverBoundaryRefinedSimplex : (sliceOver a) _⦋n + 1⦌ :=
  roofPointSliceSimplexOfFace a (SSet.yonedaEquiv (boundary.ι (0 : Fin (n + 2)) ≫ B)) F
    (dgOverBoundaryRefinedFiller_face_zero a B q s F hF)

/-- 戻した実 over 単体の零面は、元の同じ指定境界零面。 -/
lemma dgOverBoundaryRefinedSimplex_face_zero :
    (sliceOver a).δ (0 : Fin (n + 2)) (dgOverBoundaryRefinedSimplex a B q s F hF) =
      SSet.yonedaEquiv (boundary.ι (0 : Fin (n + 2)) ≫ B) :=
  roofPointSliceSimplexOfFace_face_zero a _ F _

/-- 戻した over 単体の回収は、同じ入力実充填そのもの。 -/
lemma dgOverBoundaryRefinedSimplex_simplex :
    roofPointSliceSimplex a (dgOverBoundaryRefinedSimplex a B q s F hF) = F :=
  roofPointSliceSimplexOfFace_simplex a _ F _

/-- 全ての over 面の回収単体を、同じ実充填の同じ面で照合する。 -/
lemma dgOverBoundaryRefinedSimplex_face (j : Fin (n + 2)) :
    roofPointSliceSimplex a ((sliceOver a).δ j (dgOverBoundaryRefinedSimplex a B q s F hF)) =
      SSet.stdSimplex.δ j.castSucc ≫ F :=
  roofPointSliceSimplexOfFace_face a _ F _ j

/-- 各正番号 over 面の回収は、元の同じ指定面の同じ閉始点細分である。 -/
lemma dgOverBoundaryRefinedSimplex_face_positive (j : Fin (n + 2)) (hj : j ≠ 0) :
    roofPointSliceSimplex a ((sliceOver a).δ j (dgOverBoundaryRefinedSimplex a B q s F hF)) =
      (SSet.yonedaEquiv (X := dgNerve A D)).symm
        (dgSimplexInitialRefinement A D
          (dgGeneralLastHornCanonicalFace (roofPointBoundaryHorn a B) j.castSucc
            (Fin.castSucc_ne_last j)) q
          (dgClosedTargetTransport A D s (congrArg (HornData.knownData
            (roofPointBoundaryHorn a B)).obj (dgPositiveCoface_zero j.castSucc
              (Fin.castSucc_ne_zero_iff.mpr hj)).symm))) := by
  rw [dgOverBoundaryRefinedSimplex_face,
    ← horn.ι_ι_assoc (Fin.last (n + 2)) j.castSucc (Fin.castSucc_ne_last j), hF]
  exact dgGeneralLastHornSourceRefinement_face_positive _ q s _ _
    (Fin.castSucc_ne_zero_iff.mpr hj)

end SerrePositivity.InfinityCategories
