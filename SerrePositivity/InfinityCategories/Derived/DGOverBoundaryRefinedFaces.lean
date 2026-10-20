module
public import SerrePositivity.InfinityCategories.Derived.DGOverBoundaryRefinedSimplex
public import SerrePositivity.InfinityCategories.Derived.DGOverInitialRefinementReindex

/-! # 一般回収 over 単体の正番号面を同じ元の境界面の細分へ同定する

概要：元のホーンの正番号面を実 over 境界面の回収単体へ戻し、同じ閉細分を比較する。
方針：米田表示の面公式と、追加閉射の実辺の保存を使う。
規約：全対象の等式輸送を明示。使われ方：新 apex の実分母性と共有面の厳密一致。
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

/-- 実境界の各回収単体は、元のホーンの同じ番号の指定面。 -/
lemma dgOverBoundaryCanonicalFace (j : Fin (n + 2)) :
    dgGeneralLastHornCanonicalFace (roofPointBoundaryHorn a B) j.castSucc
      (Fin.castSucc_ne_last j) =
      SSet.yonedaEquiv (roofPointSliceSimplex a (SSet.yonedaEquiv (boundary.ι j ≫ B))) := by
  refine (dgGeneralLastHornCanonicalFace_eq _ _ _).trans ?_
  have he := congrArg (SSet.yonedaEquiv (X := dgNerve A D)) (roofPointBoundaryHorn_face a B j)
  rw [SSet.yonedaEquiv_comp, horn.yonedaEquiv_ι] at he
  exact he

/-- 正番号面の回収単体の始対象は、元の同じホーン始対象。 -/
lemma dgOverBoundaryFace_source (j : Fin (n + 2)) (hj : j ≠ 0) :
    (HornData.knownData (roofPointBoundaryHorn a B)).obj 0 =
      (SSet.yonedaEquiv (roofPointSliceSimplex a (SSet.yonedaEquiv (boundary.ι j ≫ B)))).obj 0 :=
  (congrArg (HornData.knownData (roofPointBoundaryHorn a B)).obj
    (dgPositiveCoface_zero j.castSucc (Fin.castSucc_ne_zero_iff.mpr hj)).symm).trans
      (congrArg (fun t : Simplex A D (n + 1) => t.obj 0) (dgOverBoundaryCanonicalFace a B j))

/-- 全正番号面は、元の実 over 境界面の同じ閉始点細分である。 -/
lemma dgOverBoundaryRefinedSimplex_face_initial (q : D)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A)
      ((HornData.knownData (roofPointBoundaryHorn a B)).obj 0))
    (F : Δ[n + 2] ⟶ dgNerve A D)
    (hF : (horn (n + 2) (Fin.last (n + 2))).ι ≫ F =
      dgGeneralLastHornSourceRefinement (roofPointBoundaryHorn a B) q s)
    (j : Fin (n + 2)) (hj : j ≠ 0) :
    (sliceOver a).δ j (dgOverBoundaryRefinedSimplex a B q s F hF) =
      dgOverSimplexInitialRefinement A D a (SSet.yonedaEquiv (boundary.ι j ≫ B)) q
        (dgClosedTargetTransport A D s (dgOverBoundaryFace_source a B j hj)) := by
  apply roofPointSliceSimplex_injective a
  rw [dgOverBoundaryRefinedSimplex_face_positive a B q s F hF j hj,
    dgOverSimplexInitialRefinement_simplex]
  unfold dgOverSimplexInitialMap
  apply congrArg (SSet.yonedaEquiv (X := dgNerve A D)).symm
  apply dgSimplexInitialRefinement_congr (dgOverBoundaryCanonicalFace a B j) q q
  exact (dgClosedTargetTransport_edge A D s _).trans (dgClosedTargetTransport_edge A D s _).symm

end SerrePositivity.InfinityCategories
