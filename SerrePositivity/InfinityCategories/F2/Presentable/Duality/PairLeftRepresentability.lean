module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.PairUnitClassifications

/-!
概要：指定随伴の右関手は、元の全右関手圏上で固定左の単位空間を表現する。
方針：前合成随伴の Hom 同型と coslice 分類を元の保存関手圏へ制限する。
規約：同じ二変数族の固定左値との全自然な同型を作る。
使われ方：全自然変換を持つ対ごとの随伴双対性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：元の右関手は、固定左の全関手 coslice の分類図式を表現する。
方針：前合成随伴の共変 Hom 同型、表現可能 coslice、分類の底変換を順に使う。
規約：元の指定随伴の単位を用いる前合成随伴を使う。
使われ方：右保存関手圏への制限前の表現可能性。 -/
def fullLeftUnitRepresentationIso {C D : PresentableInfinityObject.{u}}
    {v : PrLFunctorSpace C D _⦋0⦌} {R : D.obj ⟶ C.obj}
    (a : QCatAdjunction (leftVertexFunctor v) R) :
    FunctorIso (covariantRepresentableInfinity (functorVertex R))
      (leftStraighteningInfinityDiagram (pullback.snd
        (sliceUnderProjection (SSet.yonedaEquiv.symm (functorVertex (𝟙 C.obj))))
        ((pre (leftVertexFunctor v)).app C.obj))) := by
  have e := adjunctionCovariantHomIso (precompositionAdjunction (Z := C.obj) a)
    (functorVertex (𝟙 C.obj))
  have hR : ((pre R).app C.obj).app (Opposite.op ⦋0⦌) (functorVertex (𝟙 C.obj)) =
      functorVertex R := by
    change functorVertex (R ≫ 𝟙 C.obj) = _
    rw [Category.comp_id]
  rw [hR] at e
  exact e ≪≫
    ((Compact.covariantRepresentableInfinity_cosliceIso (functorVertex (𝟙 C.obj))).precomp
      ((SSet.uliftFunctor.{u + 2, u + 1}).map ((pre (leftVertexFunctor v)).app C.obj))) ≪≫
    leftStraighteningInfinityDiagram_baseChangeIso
      (sliceUnderProjection (SSet.yonedaEquiv.symm (functorVertex (𝟙 C.obj))))
      ((pre (leftVertexFunctor v)).app C.obj)

/-- 概要：指定随伴の元の右頂点は、元の二変数単位族の固定左値を表現する。
方針：全関手圏での表現可能性を充満忠実な右包含で制限し、同じ底上の分類比較で戻す。
規約：core に制限せず、全自然変換に自然な同型。
使われ方：対ごとの反変作用を表現可能関手として回収する。 -/
def pairUnitHomAtLeft_representationIso {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (a : QCatAdjunction (leftVertexFunctor v) (rightVertexFunctor w)) :
    FunctorIso (covariantRepresentableInfinity w) (pairUnitHomAtLeft v) := by
  let i := rightFunctorInclusion D C
  have hi : IsFullyFaithful i := isFullyFaithful_fullSubcomplexOnVertices_ι _ _
  have hw : i.app (Opposite.op ⦋0⦌) w = functorVertex (rightVertexFunctor w) :=
    ((functorVertexEquiv D.obj C.obj).apply_symm_apply w.val).symm
  have e₁ := covariantHomComparisonIso i hi w
  rw [hw] at e₁
  let p := pullback.snd
    (sliceUnderProjection (SSet.yonedaEquiv.symm (functorVertex (𝟙 C.obj))))
    ((pre (leftVertexFunctor v)).app C.obj)
  have : LeftFibration p :=
    ⟨leftFibrations.pullback_snd _ _ (LeftFibration.mem (p :=
      sliceUnderProjection (SSet.yonedaEquiv.symm (functorVertex (𝟙 C.obj)))))⟩
  exact e₁ ≪≫
    ((fullLeftUnitRepresentationIso a).precomp ((SSet.uliftFunctor.{u + 2, u + 1}).map i)) ≪≫
    leftStraighteningInfinityDiagram_baseChangeIso p i ≪≫
    (pairUnitHomAtLeft_cosliceIso v).symm

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
