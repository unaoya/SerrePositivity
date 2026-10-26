module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NormalizationUnitCaps
public import SerrePositivity.InfinityCategories.Derived.Gluing.FirstFixedCompositionLift
public import SerrePositivity.InfinityCategories.Derived.Gluing.LastFixedCompositionLift
/-!
概要：恒等 comma の両単位補正を、元 augmentation 固定の実合成対応内の道にする。
方針：単位補正三角形の全時間の固定辺と元入力を実持ち上げへ渡す。
規約：全三角形を評価で回収する。使われ方：任意元終域の正規化境界比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type (max u v)) [DGCategory R E]
  (X Y : DGFunctorCommaObject R E E (DGFunctor.id E))
  {K : SSet.{max u v}} (f : K ⟶ DGNerve.pinchedHom R
    (DGFunctorCommaObject R E E (DGFunctor.id E)) X Y)

def dgGluingIdentityCommaPreCapCompositionPath :
    K ⊗ Δ[1] ⟶ dgGluingFirstFixedCompositionSpace
      (Edge.ofTruncated (X := dgNerve R E) (dgClosedEdge R E X.augmentation))
      (Simplex.vertex Y.source) :=
  dgGluingFirstFixedCompositionLift
    (Edge.ofTruncated (X := dgNerve R E) (dgClosedEdge R E X.augmentation))
    (Simplex.vertex Y.source)
    (fst K (Δ[1] : SSet.{max u v}) ≫ dgGluingIdentityCommaSourceIntervalFamily R E X Y f)
    (dgGluingPreUnitCapTriangleFamily R E X Y f)
    (dgGluingPreUnitCapTriangleFamily_first R E X Y f)
    (dgGluingPreUnitCapTriangleFamily_last R E X Y f)

def dgGluingIdentityCommaExitCapCompositionPath :
    K ⊗ Δ[1] ⟶ compositionCorrespondence (X := dgNerve R E)
      (Simplex.vertex X.replacement)
      (Edge.ofTruncated (X := dgNerve R E) (dgClosedEdge R E Y.augmentation)) :=
  dgGluingLastFixedCompositionLift (X := dgNerve R E) (Simplex.vertex X.replacement)
    (Edge.ofTruncated (X := dgNerve R E) (dgClosedEdge R E Y.augmentation))
    (fst K (Δ[1] : SSet.{max u v}) ≫
      dgGluingIdentityCommaReplacementIntervalFamily R E X Y f)
    (dgGluingExitUnitCapTriangleFamily R E X Y f)
    (dgGluingExitUnitCapTriangleFamily_first R E X Y f)
    (dgGluingExitUnitCapTriangleFamily_last R E X Y f)

lemma dgGluingIdentityCommaPreCapCompositionPath_over :
    dgGluingIdentityCommaPreCapCompositionPath R E X Y f ≫
      dgGluingFirstFixedCompositionSecond
        (Edge.ofTruncated (X := dgNerve R E) (dgClosedEdge R E X.augmentation))
        (Simplex.vertex Y.source) =
    fst K (Δ[1] : SSet.{max u v}) ≫ dgGluingIdentityCommaSourceIntervalFamily R E X Y f :=
  dgGluingFirstFixedCompositionLift_second _ _ _ _ _ _

lemma dgGluingIdentityCommaExitCapCompositionPath_over :
    dgGluingIdentityCommaExitCapCompositionPath R E X Y f ≫
      compositionCorrespondenceFirst (X := dgNerve R E) (Simplex.vertex X.replacement)
        (Edge.ofTruncated (X := dgNerve R E) (dgClosedEdge R E Y.augmentation)) =
    fst K (Δ[1] : SSet.{max u v}) ≫
      dgGluingIdentityCommaReplacementIntervalFamily R E X Y f :=
  dgGluingLastFixedCompositionLift_first _ _ _ _ _ _

lemma dgGluingIdentityCommaPreCapCompositionPath_evaluation :
    (Δ[2] ◁ dgGluingIdentityCommaPreCapCompositionPath R E X Y f) ≫
      dgGluingFirstFixedCompositionEvaluation
        (Edge.ofTruncated (X := dgNerve R E) (dgClosedEdge R E X.augmentation))
        (Simplex.vertex Y.source) = dgGluingPreUnitCapTriangleFamily R E X Y f :=
  dgGluingFirstFixedCompositionLift_evaluation _ _ _ _ _ _

lemma dgGluingIdentityCommaExitCapCompositionPath_evaluation :
    (Δ[2] ◁ dgGluingIdentityCommaExitCapCompositionPath R E X Y f) ≫
      compositionCorrespondenceEvaluation (X := dgNerve R E) (Simplex.vertex X.replacement)
        (Edge.ofTruncated (X := dgNerve R E) (dgClosedEdge R E Y.augmentation)) =
    dgGluingExitUnitCapTriangleFamily R E X Y f :=
  dgGluingLastFixedCompositionLift_evaluation _ _ _ _ _ _

end SerrePositivity.InfinityCategories
