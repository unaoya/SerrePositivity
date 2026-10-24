module
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaProjectionIntervalFamilies
public import SerrePositivity.InfinityCategories.Derived.Gluing.LastFixedCompositionLift
/-! # 元入力 fiber 内の実後正規化変形

概要：終側補正済み三角形族を、元 augmentation と元第一入力を保つ実ホモトピーへ移す。
方針：正規化を経た入力の鎖射影を元射影へ戻し、終辺固定の合成対応へ持ち上げる。
規約：元 Hom 入力の一致と実三角形の評価を全時間で厳密に回収する。
使われ方：後側変形を選択済み二変形との相対比較へ供給する。
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
def dgGluingPostNormalizeLastCompositionPath :
    K ⊗ Δ[1] ⟶ compositionCorrespondence (X := dgNerve R E)
    (Simplex.vertex X.replacement)
    (Edge.ofTruncated (X := dgNerve R E) (dgClosedEdge R E Y.augmentation)) :=
  dgGluingLastFixedCompositionLift (X := dgNerve R E) (Simplex.vertex X.replacement)
    (Edge.ofTruncated (X := dgNerve R E) (dgClosedEdge R E Y.augmentation))
    (fst K (Δ[1] : SSet.{max u v}) ≫ dgGluingIdentityCommaReplacementIntervalFamily R E X Y f)
    (dgGluingPostNormalizeUnitCollarTriangleFamily R E X Y f)
    (dgGluingPostNormalizeUnitCollarTriangleFamily_first_original R E X Y f)
    (dgGluingPostNormalizeUnitCollarTriangleFamily_last R E X Y f)
lemma dgGluingPostNormalizeLastCompositionPath_over :
    dgGluingPostNormalizeLastCompositionPath R E X Y f ≫
    compositionCorrespondenceFirst (X := dgNerve R E) (Simplex.vertex X.replacement)
      (Edge.ofTruncated (X := dgNerve R E) (dgClosedEdge R E Y.augmentation)) =
    fst K (Δ[1] : SSet.{max u v}) ≫ dgGluingIdentityCommaReplacementIntervalFamily R E X Y f :=
  dgGluingLastFixedCompositionLift_first _ _ _ _ _ _
lemma dgGluingPostNormalizeLastCompositionPath_evaluation :
    (Δ[2] ◁ dgGluingPostNormalizeLastCompositionPath R E X Y f) ≫
    compositionCorrespondenceEvaluation (X := dgNerve R E) (Simplex.vertex X.replacement)
      (Edge.ofTruncated (X := dgNerve R E) (dgClosedEdge R E Y.augmentation)) =
    dgGluingPostNormalizeUnitCollarTriangleFamily R E X Y f :=
  dgGluingLastFixedCompositionLift_evaluation _ _ _ _ _ _
def dgGluingPostNormalizeLastCompositionHomotopy :
    SSet.Homotopy (ι₀ ≫ dgGluingPostNormalizeLastCompositionPath R E X Y f)
    (ι₁ ≫ dgGluingPostNormalizeLastCompositionPath R E X Y f) where
  h := dgGluingPostNormalizeLastCompositionPath R E X Y f
  h₀ := rfl
  h₁ := rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property
lemma dgGluingPostNormalizeLastCompositionHomotopy_over :
    (dgGluingPostNormalizeLastCompositionHomotopy R E X Y f).h ≫
      compositionCorrespondenceFirst (X := dgNerve R E) (Simplex.vertex X.replacement)
        (Edge.ofTruncated (X := dgNerve R E) (dgClosedEdge R E Y.augmentation)) =
      fst K (Δ[1] : SSet.{max u v}) ≫ dgGluingIdentityCommaReplacementIntervalFamily R E X Y f :=
  dgGluingPostNormalizeLastCompositionPath_over R E X Y f
end SerrePositivity.InfinityCategories
