module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGVerdierRefinedOverThreeSimplex

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]
variable {P : Set D} {x : D} {K : SSet.{max u v}}
variable {f : K ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierOver A D P x : SSet.{max u v})}
variable (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGVerdierDiagramVertexCone A D P x f) (σ : K _⦋2⦌)
variable (H : ∀ i : Fin 3, Truncated.Edge.CompStruct
  (C.leg (K.δ 1 (K.δ i σ)))
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (K.δ i σ)).map ((truncation 2).map f))
  (C.leg (K.δ 0 (K.δ i σ))))
variable (q : D)
variable (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A)
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H)).obj 0))
variable (F : Δ[4] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)

/-- 回収 over 三単体の面 1 の四面体は、元の指定面の同じ閉始点細分。 -/
lemma dgVerdierDiagramRefinedOverThreeSimplex_face1
    (hF : (horn 4 4).ι ≫ F =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H) q s) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron
      ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ 1 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramRefinedOverThreeSimplex A D C σ H q s F hF)) =
        (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFace1 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H) q s) := by
  have hf := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceThreeSimplexOfFourSimplex_face _ (f.app _ σ).val F
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleRefinedFiller_face0 A D C σ H q s F hF) (1 : Fin 4)
  have hh : SSet.stdSimplex.δ (1 : Fin 5) ≫ F =
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFace1 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H) q s) := by
    rw [← horn.ι_ι_assoc (4 : Fin 5) 1 (by decide), hF,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement_face1]
  exact hf.trans hh

/-- 回収 over 三単体の面 2 の四面体は、元の指定面の同じ閉始点細分。 -/
lemma dgVerdierDiagramRefinedOverThreeSimplex_face2
    (hF : (horn 4 4).ι ≫ F =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H) q s) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron
      ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ 2 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramRefinedOverThreeSimplex A D C σ H q s F hF)) =
        (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFace2 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H) q s) := by
  have hf := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceThreeSimplexOfFourSimplex_face _ (f.app _ σ).val F
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleRefinedFiller_face0 A D C σ H q s F hF) (2 : Fin 4)
  have hh : SSet.stdSimplex.δ (2 : Fin 5) ≫ F =
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFace2 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H) q s) := by
    rw [← horn.ι_ι_assoc (4 : Fin 5) 2 (by decide), hF,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement_face2]
  exact hf.trans hh

/-- 回収 over 三単体の面 3 の四面体は、元の指定面の同じ閉始点細分。 -/
lemma dgVerdierDiagramRefinedOverThreeSimplex_face3
    (hF : (horn 4 4).ι ≫ F =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H) q s) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceTetrahedron
      ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver _).δ 3 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramRefinedOverThreeSimplex A D C σ H q s F hF)) =
        (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFace3 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H) q s) := by
  have hf := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceThreeSimplexOfFourSimplex_face _ (f.app _ σ).val F
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleRefinedFiller_face0 A D C σ H q s F hF) (3 : Fin 4)
  have hh : SSet.stdSimplex.δ (3 : Fin 5) ≫ F =
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornRefinedFace3 (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgVerdierDiagramTriangleHorn A D C σ H) q s) := by
    rw [← horn.ι_ι_assoc (4 : Fin 5) 3 (by decide), hF,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFourLastHornSourceRefinement_face3]
  exact hf.trans hh

end SerrePositivity.InfinityCategories.Project.DerivedCategories
