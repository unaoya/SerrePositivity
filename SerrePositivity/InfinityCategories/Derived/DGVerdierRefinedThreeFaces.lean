module
public import SerrePositivity.InfinityCategories.Derived.DGVerdierRefinedOverThreeSimplex

/-! # 閉細分充填から回収した over 三単体の指定三面

概要：元の零面を保つ回収三単体の残る面は、同じ指定閉始点細分の四面体を持つ。
方針：四単体からの逆回収の面公式と、細分ホーンの全指定面を接続する。
規約：対象族・cochain を選び直さない。使われ方：新 apex と有限二次整合性の照合。
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
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (dgVerdierOver A D P x : SSet.{max u v})}
variable (C : DGVerdierDiagramVertexCone A D P x f) (σ : K _⦋2⦌)
variable (H : ∀ i : Fin 3, Truncated.Edge.CompStruct
  (C.leg (K.δ 1 (K.δ i σ)))
  ((edgeOfSimplex (K.δ i σ)).map ((truncation 2).map f))
  (C.leg (K.δ 0 (K.δ i σ))))
variable (q : D)
variable (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A)
  ((HornData.knownData (dgVerdierDiagramTriangleHorn A D C σ H)).obj 0))
variable (F : Δ[4] ⟶ dgNerve A D)

/-- 回収 over 三単体の面 1 の四面体は、元の指定面の同じ閉始点細分。 -/
lemma dgVerdierDiagramRefinedOverThreeSimplex_face1
    (hF : (horn 4 4).ι ≫ F =
      dgFourLastHornSourceRefinement (dgVerdierDiagramTriangleHorn A D C σ H) q s) :
    roofPointSliceTetrahedron
      ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x))
      ((sliceOver _).δ 1 (dgVerdierDiagramRefinedOverThreeSimplex A D C σ H q s F hF)) =
        (SSet.yonedaEquiv (X := dgNerve A D)).symm
          (dgFourLastHornRefinedFace1 (dgVerdierDiagramTriangleHorn A D C σ H) q s) := by
  have hf := roofPointSliceThreeSimplexOfFourSimplex_face _ (f.app _ σ).val F
    (dgVerdierDiagramTriangleRefinedFiller_face0 A D C σ H q s F hF) (1 : Fin 4)
  have hh : SSet.stdSimplex.δ (1 : Fin 5) ≫ F =
      (SSet.yonedaEquiv (X := dgNerve A D)).symm
        (dgFourLastHornRefinedFace1 (dgVerdierDiagramTriangleHorn A D C σ H) q s) := by
    rw [← horn.ι_ι_assoc (4 : Fin 5) 1 (by decide), hF,
      dgFourLastHornSourceRefinement_face1]
  exact hf.trans hh

/-- 回収 over 三単体の面 2 の四面体は、元の指定面の同じ閉始点細分。 -/
lemma dgVerdierDiagramRefinedOverThreeSimplex_face2
    (hF : (horn 4 4).ι ≫ F =
      dgFourLastHornSourceRefinement (dgVerdierDiagramTriangleHorn A D C σ H) q s) :
    roofPointSliceTetrahedron
      ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x))
      ((sliceOver _).δ 2 (dgVerdierDiagramRefinedOverThreeSimplex A D C σ H q s F hF)) =
        (SSet.yonedaEquiv (X := dgNerve A D)).symm
          (dgFourLastHornRefinedFace2 (dgVerdierDiagramTriangleHorn A D C σ H) q s) := by
  have hf := roofPointSliceThreeSimplexOfFourSimplex_face _ (f.app _ σ).val F
    (dgVerdierDiagramTriangleRefinedFiller_face0 A D C σ H q s F hF) (2 : Fin 4)
  have hh : SSet.stdSimplex.δ (2 : Fin 5) ≫ F =
      (SSet.yonedaEquiv (X := dgNerve A D)).symm
        (dgFourLastHornRefinedFace2 (dgVerdierDiagramTriangleHorn A D C σ H) q s) := by
    rw [← horn.ι_ι_assoc (4 : Fin 5) 2 (by decide), hF,
      dgFourLastHornSourceRefinement_face2]
  exact hf.trans hh

/-- 回収 over 三単体の面 3 の四面体は、元の指定面の同じ閉始点細分。 -/
lemma dgVerdierDiagramRefinedOverThreeSimplex_face3
    (hF : (horn 4 4).ι ≫ F =
      dgFourLastHornSourceRefinement (dgVerdierDiagramTriangleHorn A D C σ H) q s) :
    roofPointSliceTetrahedron
      ((SSet.yonedaEquiv (X := dgNerve A D)).symm (Simplex.vertex x))
      ((sliceOver _).δ 3 (dgVerdierDiagramRefinedOverThreeSimplex A D C σ H q s F hF)) =
        (SSet.yonedaEquiv (X := dgNerve A D)).symm
          (dgFourLastHornRefinedFace3 (dgVerdierDiagramTriangleHorn A D C σ H) q s) := by
  have hf := roofPointSliceThreeSimplexOfFourSimplex_face _ (f.app _ σ).val F
    (dgVerdierDiagramTriangleRefinedFiller_face0 A D C σ H q s F hF) (3 : Fin 4)
  have hh : SSet.stdSimplex.δ (3 : Fin 5) ≫ F =
      (SSet.yonedaEquiv (X := dgNerve A D)).symm
        (dgFourLastHornRefinedFace3 (dgVerdierDiagramTriangleHorn A D C σ H) q s) := by
    rw [← horn.ι_ι_assoc (4 : Fin 5) 3 (by decide), hF,
      dgFourLastHornSourceRefinement_face3]
  exact hf.trans hh

end SerrePositivity.InfinityCategories
