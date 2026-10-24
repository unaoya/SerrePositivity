module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ExitUnitCollarTriangles
public import SerrePositivity.InfinityCategories.Derived.Gluing.LastFixedCompositionLift
/-! # 元入力 fiber 内の実終側合成変形

概要：標準終側合成面の補正済み三角形族を、元 augmentation と元第一入力を保つ実ホモトピーへ移す。
方針：元 Hom 入力の鎖射影を保持し、終辺固定の合成対応へ持ち上げる。
規約：元 Hom 入力の一致と実三角形の評価を全時間で厳密に回収する。
使われ方：元の第二三角形の変形を、選択済み二変形との相対比較へ供給する。
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
def dgGluingExitLastCompositionPath :
    K ⊗ Δ[1] ⟶ compositionCorrespondence (X := dgNerve R E)
    (Simplex.vertex X.replacement)
    (Edge.ofTruncated (X := dgNerve R E) (dgClosedEdge R E Y.augmentation)) :=
  dgGluingLastFixedCompositionLift (X := dgNerve R E) (Simplex.vertex X.replacement)
    (Edge.ofTruncated (X := dgNerve R E) (dgClosedEdge R E Y.augmentation))
    (fst K (Δ[1] : SSet.{max u v}) ≫ dgGluingIdentityCommaReplacementIntervalFamily R E X Y f)
    (dgGluingExitUnitCollarTriangleFamily R E X Y f)
    (dgGluingExitUnitCollarTriangleFamily_first_original R E X Y f)
    (dgGluingExitUnitCollarTriangleFamily_last R E X Y f)
lemma dgGluingExitLastCompositionPath_over :
    dgGluingExitLastCompositionPath R E X Y f ≫
    compositionCorrespondenceFirst (X := dgNerve R E) (Simplex.vertex X.replacement)
      (Edge.ofTruncated (X := dgNerve R E) (dgClosedEdge R E Y.augmentation)) =
    fst K (Δ[1] : SSet.{max u v}) ≫ dgGluingIdentityCommaReplacementIntervalFamily R E X Y f :=
  dgGluingLastFixedCompositionLift_first _ _ _ _ _ _
lemma dgGluingExitLastCompositionPath_evaluation :
    (Δ[2] ◁ dgGluingExitLastCompositionPath R E X Y f) ≫
    compositionCorrespondenceEvaluation (X := dgNerve R E) (Simplex.vertex X.replacement)
      (Edge.ofTruncated (X := dgNerve R E) (dgClosedEdge R E Y.augmentation)) =
    dgGluingExitUnitCollarTriangleFamily R E X Y f :=
  dgGluingLastFixedCompositionLift_evaluation _ _ _ _ _ _
def dgGluingExitLastCompositionHomotopy :
    SSet.Homotopy (ι₀ ≫ dgGluingExitLastCompositionPath R E X Y f)
    (ι₁ ≫ dgGluingExitLastCompositionPath R E X Y f) where
  h := dgGluingExitLastCompositionPath R E X Y f
  h₀ := rfl
  h₁ := rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property
lemma dgGluingExitLastCompositionHomotopy_over :
    (dgGluingExitLastCompositionHomotopy R E X Y f).h ≫
      compositionCorrespondenceFirst (X := dgNerve R E) (Simplex.vertex X.replacement)
        (Edge.ofTruncated (X := dgNerve R E) (dgClosedEdge R E Y.augmentation)) =
      fst K (Δ[1] : SSet.{max u v}) ≫ dgGluingIdentityCommaReplacementIntervalFamily R E X Y f :=
  dgGluingExitLastCompositionPath_over R E X Y f
end SerrePositivity.InfinityCategories
