module
public import SerrePositivity.InfinityCategories.Derived.Gluing.NativeUnitCollarInputs
public import SerrePositivity.InfinityCategories.Derived.Gluing.FirstFixedCompositionLift
public import SerrePositivity.InfinityCategories.Derived.Gluing.LastFixedCompositionLift

/-! # native 単位補正族の実合成対応内の道

概要：四つの native 補正族を、元 augmentation と元係数入力を保つ実合成対応へ持ち上げる。
方針：同じ三角形族と全時間の二辺の等式を、固定辺の合成対応へ渡す。
規約：元 Hom 入力の一致と実三角形の評価を厳密に回収する。
使われ方：元入力付き fiber への持ち上げと、選択済み変形との相対比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
local notation "P" => dgGluingNativePinchedHomParameter R C D M X Y

def dgGluingNativePreCollarCompositionPath :
    P ⊗ Δ[1] ⟶
      dgGluingFirstFixedCompositionSpace (dgGluingDerivedAugmentationEdge R C D M X)
    ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
      (ULift.up (Simplex.vertex Y.right))) :=
  dgGluingFirstFixedCompositionLift (dgGluingDerivedAugmentationEdge R C D M X)
    ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
      (ULift.up (Simplex.vertex Y.right)))
    (fst P (Δ[1] : SSet.{max (u + 1) v w}) ≫
      dgGluingNativeHomModelMap R C D M X Y ≫
        dgGluingHomDerivedRightCoefficientInput R C D M X Y)
    (dgGluingNativePreNormalizeUnitCollarTriangleFamily R C D M X Y)
    (by simpa only [Category.assoc] using
      dgGluingNativePreNormalizeUnitCollarTriangleFamily_first R C D M X Y)
    (by simpa only [Category.assoc] using
      dgGluingNativePreNormalizeUnitCollarTriangleFamily_last_input R C D M X Y)

lemma dgGluingNativePreCollarCompositionPath_input :
    dgGluingNativePreCollarCompositionPath R C D M X Y ≫
      dgGluingFirstFixedCompositionSecond (dgGluingDerivedAugmentationEdge R C D M X)
      ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
      (ULift.up (Simplex.vertex Y.right))) =
    fst P (Δ[1] : SSet.{max (u + 1) v w}) ≫
      dgGluingNativeHomModelMap R C D M X Y ≫
        dgGluingHomDerivedRightCoefficientInput R C D M X Y :=
  dgGluingFirstFixedCompositionLift_second _ _ _ _ _ _

lemma dgGluingNativePreCollarCompositionPath_evaluation :
    (Δ[2] ◁ dgGluingNativePreCollarCompositionPath R C D M X Y) ≫
      dgGluingFirstFixedCompositionEvaluation (dgGluingDerivedAugmentationEdge R C D M X)
      ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
      (ULift.up (Simplex.vertex Y.right))) =
    dgGluingNativePreNormalizeUnitCollarTriangleFamily R C D M X Y :=
  dgGluingFirstFixedCompositionLift_evaluation _ _ _ _ _ _

def dgGluingNativePreCapCompositionPath :
    P ⊗ Δ[1] ⟶
      dgGluingFirstFixedCompositionSpace (dgGluingDerivedAugmentationEdge R C D M X)
    ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
      (ULift.up (Simplex.vertex Y.right))) :=
  dgGluingFirstFixedCompositionLift (dgGluingDerivedAugmentationEdge R C D M X)
    ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
      (ULift.up (Simplex.vertex Y.right)))
    (fst P (Δ[1] : SSet.{max (u + 1) v w}) ≫
      dgGluingNativeHomModelMap R C D M X Y ≫
        dgGluingHomDerivedRightCoefficientInput R C D M X Y)
    (dgGluingNativePreUnitCapTriangleFamily R C D M X Y)
    (by simpa only [Category.assoc] using
      dgGluingNativePreUnitCapTriangleFamily_first R C D M X Y)
    (by simpa only [Category.assoc] using
      dgGluingNativePreUnitCapTriangleFamily_last_input R C D M X Y)

lemma dgGluingNativePreCapCompositionPath_input :
    dgGluingNativePreCapCompositionPath R C D M X Y ≫
      dgGluingFirstFixedCompositionSecond (dgGluingDerivedAugmentationEdge R C D M X)
      ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
      (ULift.up (Simplex.vertex Y.right))) =
    fst P (Δ[1] : SSet.{max (u + 1) v w}) ≫
      dgGluingNativeHomModelMap R C D M X Y ≫
        dgGluingHomDerivedRightCoefficientInput R C D M X Y :=
  dgGluingFirstFixedCompositionLift_second _ _ _ _ _ _

lemma dgGluingNativePreCapCompositionPath_evaluation :
    (Δ[2] ◁ dgGluingNativePreCapCompositionPath R C D M X Y) ≫
      dgGluingFirstFixedCompositionEvaluation (dgGluingDerivedAugmentationEdge R C D M X)
      ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
      (ULift.up (Simplex.vertex Y.right))) =
    dgGluingNativePreUnitCapTriangleFamily R C D M X Y :=
  dgGluingFirstFixedCompositionLift_evaluation _ _ _ _ _ _

def dgGluingNativeExitCollarCompositionPath :
    P ⊗ Δ[1] ⟶
      compositionCorrespondence (X :=
        ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
      (dgModuleDerivedInfinityCategory R C)))
    ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
      (ULift.up (Simplex.vertex X.left))) (dgGluingDerivedAugmentationEdge R C D M Y) :=
  dgGluingLastFixedCompositionLift (X :=
        ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
      (dgModuleDerivedInfinityCategory R C)))
    ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
      (ULift.up (Simplex.vertex X.left))) (dgGluingDerivedAugmentationEdge R C D M Y)
    (fst P (Δ[1] : SSet.{max (u + 1) v w}) ≫
      dgGluingNativeHomModelMap R C D M X Y ≫
        dgGluingHomDerivedLeftCoefficientInput R C D M X Y)
    (dgGluingNativeExitUnitCollarTriangleFamily R C D M X Y)
    (by simpa only [Category.assoc] using
      dgGluingNativeExitUnitCollarTriangleFamily_first_input R C D M X Y)
    (by simpa only [Category.assoc] using
      dgGluingNativeExitUnitCollarTriangleFamily_last R C D M X Y)

lemma dgGluingNativeExitCollarCompositionPath_input :
    dgGluingNativeExitCollarCompositionPath R C D M X Y ≫
      compositionCorrespondenceFirst (X :=
        ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
      (dgModuleDerivedInfinityCategory R C)))
      ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
      (ULift.up (Simplex.vertex X.left))) (dgGluingDerivedAugmentationEdge R C D M Y) =
    fst P (Δ[1] : SSet.{max (u + 1) v w}) ≫
      dgGluingNativeHomModelMap R C D M X Y ≫
        dgGluingHomDerivedLeftCoefficientInput R C D M X Y :=
  dgGluingLastFixedCompositionLift_first _ _ _ _ _ _

lemma dgGluingNativeExitCollarCompositionPath_evaluation :
    (Δ[2] ◁ dgGluingNativeExitCollarCompositionPath R C D M X Y) ≫
      compositionCorrespondenceEvaluation (X :=
        ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
      (dgModuleDerivedInfinityCategory R C)))
      ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
      (ULift.up (Simplex.vertex X.left))) (dgGluingDerivedAugmentationEdge R C D M Y) =
    dgGluingNativeExitUnitCollarTriangleFamily R C D M X Y :=
  dgGluingLastFixedCompositionLift_evaluation _ _ _ _ _ _

def dgGluingNativeExitCapCompositionPath :
    P ⊗ Δ[1] ⟶
      compositionCorrespondence (X :=
        ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
      (dgModuleDerivedInfinityCategory R C)))
    ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
      (ULift.up (Simplex.vertex X.left))) (dgGluingDerivedAugmentationEdge R C D M Y) :=
  dgGluingLastFixedCompositionLift (X :=
        ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
      (dgModuleDerivedInfinityCategory R C)))
    ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
      (ULift.up (Simplex.vertex X.left))) (dgGluingDerivedAugmentationEdge R C D M Y)
    (fst P (Δ[1] : SSet.{max (u + 1) v w}) ≫
      dgGluingNativeHomModelMap R C D M X Y ≫
        dgGluingHomDerivedLeftCoefficientInput R C D M X Y)
    (dgGluingNativeExitUnitCapTriangleFamily R C D M X Y)
    (by simpa only [Category.assoc] using
      dgGluingNativeExitUnitCapTriangleFamily_first_input R C D M X Y)
    (by simpa only [Category.assoc] using
      dgGluingNativeExitUnitCapTriangleFamily_last R C D M X Y)

lemma dgGluingNativeExitCapCompositionPath_input :
    dgGluingNativeExitCapCompositionPath R C D M X Y ≫
      compositionCorrespondenceFirst (X :=
        ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
      (dgModuleDerivedInfinityCategory R C)))
      ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
      (ULift.up (Simplex.vertex X.left))) (dgGluingDerivedAugmentationEdge R C D M Y) =
    fst P (Δ[1] : SSet.{max (u + 1) v w}) ≫
      dgGluingNativeHomModelMap R C D M X Y ≫
        dgGluingHomDerivedLeftCoefficientInput R C D M X Y :=
  dgGluingLastFixedCompositionLift_first _ _ _ _ _ _

lemma dgGluingNativeExitCapCompositionPath_evaluation :
    (Δ[2] ◁ dgGluingNativeExitCapCompositionPath R C D M X Y) ≫
      compositionCorrespondenceEvaluation (X :=
        ((SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
      (dgModuleDerivedInfinityCategory R C)))
      ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
      (ULift.up (Simplex.vertex X.left))) (dgGluingDerivedAugmentationEdge R C D M Y) =
    dgGluingNativeExitUnitCapTriangleFamily R C D M X Y :=
  dgGluingLastFixedCompositionLift_evaluation _ _ _ _ _ _
end SerrePositivity.InfinityCategories
