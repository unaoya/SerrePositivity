module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomTriangleHomotopyFamilies
/-! # 元入力と実三角形による入力 fiber の外延性

概要：元 Hom 入力と三角形評価の一致から、入力 fiber への写像全体を同定する。
方針：二段の引き戻しの外延性と curry の単射性を使う。
規約：端点や対角だけの一致で代用しない。
使われ方：実補正道の両端を、正本と係数側の指定した入力付き持ち上げへ同定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
lemma dgGluingDerivedFirstInputTriangle_hom_ext {A : SSet.{max (u + 1) v w}}
    {f g : A ⟶ dgGluingDerivedFirstCompositionInputFiber R C D M X Y}
    (ht : (Δ[2] ◁ f) ≫ dgGluingDerivedFirstInputTriangleEvaluation R C D M X Y =
      (Δ[2] ◁ g) ≫ dgGluingDerivedFirstInputTriangleEvaluation R C D M X Y)
    (hp : f ≫ dgGluingDerivedFirstCompositionInputProjection R C D M X Y =
      g ≫ dgGluingDerivedFirstCompositionInputProjection R C D M X Y) : f = g := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · apply uncurry_injective
      simpa only [uncurry_natural_left, whiskerLeft_comp, Category.assoc,
        dgGluingDerivedFirstInputTriangleEvaluation,
        dgGluingFirstFixedCompositionEvaluation] using ht
    · change (f ≫ pullback.fst _ _) ≫
        dgGluingFirstFixedCompositionSecond (dgGluingDerivedAugmentationEdge R C D M X)
          ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
            (ULift.up (Simplex.vertex Y.right))) =
        (g ≫ pullback.fst _ _) ≫
        dgGluingFirstFixedCompositionSecond (dgGluingDerivedAugmentationEdge R C D M X)
          ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
            (ULift.up (Simplex.vertex Y.right)))
      simp only [Category.assoc, pullback.condition]
      simpa only [dgGluingDerivedFirstCompositionInputProjection, Category.assoc] using
        congrArg (fun k => k ≫ dgGluingDerivedRightCoefficientInput R C D M X Y) hp
  · exact hp

lemma dgGluingDerivedLastInputTriangle_hom_ext {A : SSet.{max (u + 1) v w}}
    {f g : A ⟶ dgGluingDerivedLastCompositionInputFiber R C D M X Y}
    (ht : (Δ[2] ◁ f) ≫ dgGluingDerivedLastInputTriangleEvaluation R C D M X Y =
      (Δ[2] ◁ g) ≫ dgGluingDerivedLastInputTriangleEvaluation R C D M X Y)
    (hp : f ≫ dgGluingDerivedLastCompositionInputProjection R C D M X Y =
      g ≫ dgGluingDerivedLastCompositionInputProjection R C D M X Y) : f = g := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · apply uncurry_injective
      simpa only [uncurry_natural_left, whiskerLeft_comp, Category.assoc,
        dgGluingDerivedLastInputTriangleEvaluation, compositionCorrespondenceEvaluation] using ht
    · change (f ≫ pullback.fst _ _) ≫
        compositionCorrespondenceFirst
          (X := (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
            (dgModuleDerivedInfinityCategory R C))
          ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
            (ULift.up (Simplex.vertex X.left)))
          (dgGluingDerivedAugmentationEdge R C D M Y) =
        (g ≫ pullback.fst _ _) ≫
        compositionCorrespondenceFirst
          (X := (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
            (dgModuleDerivedInfinityCategory R C))
          ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
            (ULift.up (Simplex.vertex X.left)))
          (dgGluingDerivedAugmentationEdge R C D M Y)
      simp only [Category.assoc, pullback.condition]
      simpa only [dgGluingDerivedLastCompositionInputProjection, Category.assoc] using
        congrArg (fun k => k ≫ dgGluingDerivedLeftCoefficientInput R C D M X Y) hp
  · exact hp


lemma dgGluingLaxHomFirstCompositionInputLift_triangle :
    (Δ[2] ◁ dgGluingLaxHomFirstCompositionInputLift R C D M X Y) ≫
      dgGluingDerivedFirstInputTriangleEvaluation R C D M X Y =
      (dgGluingLaxHomArrowTriangles R C D M X Y).first := by
  rw [dgGluingDerivedFirstInputTriangleEvaluation, ← Category.assoc, ← whiskerLeft_comp,
    dgGluingLaxHomFirstCompositionInputLift_composition R C D M X Y,
    dgGluingLaxHomArrowCompositionComparison_first_triangle R C D M X Y]

lemma dgGluingLaxHomLastCompositionInputLift_triangle :
    (Δ[2] ◁ dgGluingLaxHomLastCompositionInputLift R C D M X Y) ≫
      dgGluingDerivedLastInputTriangleEvaluation R C D M X Y =
      (dgGluingLaxHomArrowTriangles R C D M X Y).second := by
  rw [dgGluingDerivedLastInputTriangleEvaluation, ← Category.assoc, ← whiskerLeft_comp,
    dgGluingLaxHomLastCompositionInputLift_composition R C D M X Y,
    dgGluingLaxHomArrowCompositionComparison_last_triangle R C D M X Y]

lemma dgGluingHomDerivedFirstCompositionInputLift_triangle :
    (Δ[2] ◁ dgGluingHomDerivedFirstCompositionInputLift R C D M X Y) ≫
      dgGluingDerivedFirstInputTriangleEvaluation R C D M X Y =
      dgGluingHomDerivedRightCoefficientTriangle R C D M X Y := by
  rw [dgGluingDerivedFirstInputTriangleEvaluation, ← Category.assoc, ← whiskerLeft_comp,
    dgGluingHomDerivedFirstCompositionInputLift_composition R C D M X Y,
    dgGluingHomDerivedFirstComposition_triangle R C D M X Y]

lemma dgGluingHomDerivedLastCompositionInputLift_triangle :
    (Δ[2] ◁ dgGluingHomDerivedLastCompositionInputLift R C D M X Y) ≫
      dgGluingDerivedLastInputTriangleEvaluation R C D M X Y =
      dgGluingHomDerivedLeftCoefficientTriangle R C D M X Y := by
  rw [dgGluingDerivedLastInputTriangleEvaluation, ← Category.assoc, ← whiskerLeft_comp,
    dgGluingHomDerivedLastCompositionInputLift_composition R C D M X Y,
    dgGluingHomDerivedLastComposition_triangle R C D M X Y]
end SerrePositivity.InfinityCategories
