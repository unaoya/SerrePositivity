module
public import SerrePositivity.InfinityCategories.Derived.DGOverTwoSimplexInitialRefinement
public import SerrePositivity.InfinityCategories.Derived.DGInitialRefinementPositiveFaces
public import SerrePositivity.InfinityCategories.Derived.DGInitialRefinementCongruence
public import SerrePositivity.InfinityCategories.Derived.DGInitialRefinementTriangle

/-! # 実 over 二単体の閉始点細分の二つの脚面

概要：細分後の正番号二面の回収三角形は、元の脚面の同じ閉始点細分。
方針：四面体の面公式と一般細分の正番号面との可換性、元の対象等式を接続する。
規約：追加閉実辺を保持。使われ方：辺錐の二脚と固定頂点脚の一致。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
variable (x : D)
variable (σ : (sliceOver ((SSet.yonedaEquiv (X := dgNerve A D)).symm
  (Simplex.vertex x))) _⦋2⦌) (q : D)
variable (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A)
  (((SSet.yonedaEquiv (X := dgNerve A D)) (roofPointSliceTetrahedron _ σ)).obj 0))


/-- 元の正番号面の回収三角形は、元の回収四面体の対応する正番号面。 -/
lemma dgOverTwoSimplexPositiveFace_triangle (i : Fin 2) :
    (dgNerve A D).δ i.succ.castSucc (SSet.yonedaEquiv (roofPointSliceTetrahedron _ σ)) =
      SSet.yonedaEquiv (roofPointSliceTriangle _ ((sliceOver _).δ i.succ σ)) := by
  have h := congrArg (SSet.yonedaEquiv (X := dgNerve A D))
    (roofPointSliceTetrahedron_face _ σ i.succ)
  rw [stdSimplex.yonedaEquiv_δ_comp] at h
  exact h

/-- 元の各正番号面の回収三角形の始対象は、同じ回収四面体の始対象。 -/
lemma dgOverTwoSimplexPositiveFace_source (i : Fin 2) :
    (SSet.yonedaEquiv (roofPointSliceTetrahedron _ σ)).obj 0 =
      (SSet.yonedaEquiv (roofPointSliceTriangle _ ((sliceOver _).δ i.succ σ))).obj 0 := by
  fin_cases i
  · exact congrArg (fun t : Simplex A D 2 => t.obj 0)
      (dgOverTwoSimplexPositiveFace_triangle A D x σ 0)
  · exact congrArg (fun t : Simplex A D 2 => t.obj 0)
      (dgOverTwoSimplexPositiveFace_triangle A D x σ 1)

/-- 細分後の各脚面は、元の同じ脚三角形の同じ閉始点細分として回収される。 -/
lemma dgOverTwoSimplexInitialRefinement_face_positive (i : Fin 2) :
    roofPointSliceTriangle _ ((sliceOver _).δ i.succ
      (dgOverTwoSimplexInitialRefinement A D x σ q s)) =
      (SSet.yonedaEquiv (X := dgNerve A D)).symm
        (dgSimplexInitialRefinement A D
          (SSet.yonedaEquiv (roofPointSliceTriangle _ ((sliceOver _).δ i.succ σ))) q
          (dgClosedTargetTransport A D s (dgOverTwoSimplexPositiveFace_source A D x σ i))) := by
  have hf := roofPointSliceTwoSimplexOfTetrahedron_face _ (edgeOfSimplex ((sliceOver _).δ 0 σ))
    (dgOverTwoSimplexInitialTetrahedron A D x σ q s)
    (dgOverTwoSimplexInitialTetrahedron_face0 A D x σ q s) i.succ
  have hc := dgSimplexInitialRefinement_congr
    (dgOverTwoSimplexPositiveFace_triangle A D x σ i) q q s
    (dgClosedTargetTransport A D s (dgOverTwoSimplexPositiveFace_source A D x σ i))
    (dgClosedTargetTransport_edge A D s _).symm
  fin_cases i
  · have hp := dgSimplexInitialRefinement_face_positive A D
      (SSet.yonedaEquiv (roofPointSliceTetrahedron _ σ)) q s (1 : Fin 4) (by decide)
    simp only [dgClosedTargetTransport, eqToHom_refl, Category.comp_id] at hp
    have hh : SSet.stdSimplex.δ (1 : Fin 4) ≫ dgOverTwoSimplexInitialTetrahedron A D x σ q s =
        (SSet.yonedaEquiv (X := dgNerve A D)).symm
          (dgSimplexInitialRefinement A D
            (SSet.yonedaEquiv (roofPointSliceTriangle _ ((sliceOver _).δ 1 σ))) q
            (dgClosedTargetTransport A D s (dgOverTwoSimplexPositiveFace_source A D x σ 0))) := by
      unfold dgOverTwoSimplexInitialTetrahedron
      rw [stdSimplex.δ_comp_yonedaEquiv_symm]
      exact congrArg (SSet.yonedaEquiv (X := dgNerve A D)).symm (hp.trans hc)
    exact hf.trans hh
  · have hp := dgSimplexInitialRefinement_face_positive A D
      (SSet.yonedaEquiv (roofPointSliceTetrahedron _ σ)) q s (2 : Fin 4) (by decide)
    simp only [dgClosedTargetTransport, eqToHom_refl, Category.comp_id] at hp
    have hh : SSet.stdSimplex.δ (2 : Fin 4) ≫ dgOverTwoSimplexInitialTetrahedron A D x σ q s =
        (SSet.yonedaEquiv (X := dgNerve A D)).symm
          (dgSimplexInitialRefinement A D
            (SSet.yonedaEquiv (roofPointSliceTriangle _ ((sliceOver _).δ 2 σ))) q
            (dgClosedTargetTransport A D s (dgOverTwoSimplexPositiveFace_source A D x σ 1))) := by
      unfold dgOverTwoSimplexInitialTetrahedron
      rw [stdSimplex.δ_comp_yonedaEquiv_symm]
      exact congrArg (SSet.yonedaEquiv (X := dgNerve A D)).symm (hp.trans hc)
    exact hf.trans hh

end SerrePositivity.InfinityCategories
