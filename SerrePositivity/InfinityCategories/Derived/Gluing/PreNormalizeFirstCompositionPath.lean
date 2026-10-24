module
public import SerrePositivity.InfinityCategories.Derived.Gluing.PreNormalizeUnitCollarTriangles
public import SerrePositivity.InfinityCategories.Derived.Gluing.FirstFixedCompositionLift

/-! # 元入力 fiber 内の実前正規化変形

概要：側面補正済み三角形族を、元 augmentation の合成対応内の実ホモトピーへ持ち上げる。
方針：全時間で指定始辺と元第二入力を保つ等式を、同じ合成対応の引き戻しへ渡す。
規約：実三角形の評価と元 Hom 入力の一致を厳密に回収する。
使われ方：正本第一三角形と補正端の間の変形を、選択済み変形との相対比較へ供給する。
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
local notation "Q" => DGFunctorCommaObject R E E (DGFunctor.id E)
def dgGluingPreNormalizeFirstCompositionPath : K ⊗ Δ[1] ⟶ dgGluingFirstFixedCompositionSpace
    (Edge.ofTruncated (X := dgNerve R E) (dgClosedEdge R E X.augmentation))
      (Simplex.vertex Y.source) :=
  dgGluingFirstFixedCompositionLift
    (Edge.ofTruncated (X := dgNerve R E) (dgClosedEdge R E X.augmentation))
    (Simplex.vertex Y.source) (fst K (Δ[1] : SSet.{max u v}) ≫
      dgGluingIdentityCommaSourceIntervalFamily R E X Y f)
    (dgGluingPreNormalizeUnitCollarTriangleFamily R E X Y f)
    (dgGluingPreNormalizeUnitCollarTriangleFamily_first R E X Y f)
    (dgGluingPreNormalizeUnitCollarTriangleFamily_last_input R E X Y f)
lemma dgGluingPreNormalizeFirstCompositionPath_over :
    dgGluingPreNormalizeFirstCompositionPath R E X Y f ≫ dgGluingFirstFixedCompositionSecond
      (Edge.ofTruncated (X := dgNerve R E) (dgClosedEdge R E X.augmentation))
      (Simplex.vertex Y.source) =
    fst K (Δ[1] : SSet.{max u v}) ≫ dgGluingIdentityCommaSourceIntervalFamily R E X Y f :=
  dgGluingFirstFixedCompositionLift_second _ _ _ _ _ _
lemma dgGluingPreNormalizeFirstCompositionPath_evaluation :
    (Δ[2] ◁ dgGluingPreNormalizeFirstCompositionPath R E X Y f) ≫
      dgGluingFirstFixedCompositionEvaluation
      (Edge.ofTruncated (X := dgNerve R E) (dgClosedEdge R E X.augmentation))
      (Simplex.vertex Y.source) =
    dgGluingPreNormalizeUnitCollarTriangleFamily R E X Y f :=
  dgGluingFirstFixedCompositionLift_evaluation _ _ _ _ _ _


def dgGluingPreNormalizeFirstCompositionHomotopy :
    SSet.Homotopy (ι₀ ≫ dgGluingPreNormalizeFirstCompositionPath R E X Y f)
      (ι₁ ≫ dgGluingPreNormalizeFirstCompositionPath R E X Y f) where
  h := dgGluingPreNormalizeFirstCompositionPath R E X Y f
  h₀ := rfl
  h₁ := rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

lemma dgGluingPreNormalizeFirstCompositionHomotopy_over :
    (dgGluingPreNormalizeFirstCompositionHomotopy R E X Y f).h ≫
      dgGluingFirstFixedCompositionSecond
        (Edge.ofTruncated (X := dgNerve R E) (dgClosedEdge R E X.augmentation))
        (Simplex.vertex Y.source) =
      fst K (Δ[1] : SSet.{max u v}) ≫ dgGluingIdentityCommaSourceIntervalFamily R E X Y f :=
  dgGluingPreNormalizeFirstCompositionPath_over R E X Y f
end SerrePositivity.InfinityCategories
