module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.PairUnitRightRestriction
public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.PairLeftRepresentability
public import SerrePositivity.InfinityCategories.HomotopyLimits.PostcompositionAdjunction

/-!
概要：指定随伴の左関手は、元の全左関手圏上で固定右の単位空間を表現する。
方針：固定右 coslice の分類を元の全二変数族に接続し、後合成随伴を適用する。
規約：元の非可逆な自然変換を全て保持する。
使われ方：同じ反変随伴関手の充満忠実性への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：固定右 coslice を元の全左保存関手圏へ制限した空間。
方針：後合成への単位 coslice を元の左包含で引き戻す。
規約：左関手の全自然変換を底に持つ。
使われ方：右固定値の表現可能性。 -/
def PreservingRightUnitCoslice {C D : PresentableInfinityObject.{u}}
    (w : PrRFunctorSpace D C _⦋0⦌) : SSet.{u + 1} :=
  pullback (pullback.snd
    (sliceUnderProjection (SSet.yonedaEquiv.symm (functorVertex (𝟙 C.obj))))
    ((ihom C.obj).map (rightVertexFunctor w))) (leftFunctorInclusion C D)

/-- 概要：保存条件付きの固定右単位空間の元の左関手への射影。
方針：引き戻しの第二脚を取る。
規約：元の全左関手圏を底にする。
使われ方：同じ底上での分類。 -/
def preservingRightUnitProjection {C D : PresentableInfinityObject.{u}}
    (w : PrRFunctorSpace D C _⦋0⦌) : PreservingRightUnitCoslice w ⟶ PrLFunctorSpace C D :=
  pullback.snd _ _

instance preservingRightUnitProjection_leftFibration {C D : PresentableInfinityObject.{u}}
    (w : PrRFunctorSpace D C _⦋0⦌) : LeftFibration (preservingRightUnitProjection w) := by
  let p := sliceUnderProjection (SSet.yonedaEquiv.symm (functorVertex (𝟙 C.obj)))
  let f := (ihom C.obj).map (rightVertexFunctor w)
  have : LeftFibration (pullback.snd p f) :=
    ⟨leftFibrations.pullback_snd _ _ (LeftFibration.mem (p := p))⟩
  exact ⟨leftFibrations.pullback_snd _ _ (LeftFibration.mem (p := pullback.snd p f))⟩

instance preservingRightUnitCoslice_quasicategory {C D : PresentableInfinityObject.{u}}
    (w : PrRFunctorSpace D C _⦋0⦌) : Quasicategory (PreservingRightUnitCoslice w) :=
  quasicategory_of_innerFibration (preservingRightUnitProjection w)

/-- 概要：元の全単位族の固定右制限は元の保存条件付き coslice と厳密に同型。
方針：引き戻しの二通りの貼り合わせを元の固定右合成の等式で接続する。
規約：底の左関手を変えない。
使われ方：同じ分類図式を普遍単位へ比較する。 -/
def pairFixedRightCosliceIso {C D : PresentableInfinityObject.{u}}
    (w : PrRFunctorSpace D C _⦋0⦌) :
    pullback (covariantPairUnitProjection C D) (pairFixedRightBase w) ≅
      PreservingRightUnitCoslice w :=
  pullbackLeftPullbackSndIso _ _ _ ≪≫
    pullback.congrHom rfl (pairFixedRightBase_composition w) ≪≫
      (pullbackLeftPullbackSndIso _ _ _).symm

/-- 概要：同じ固定右比較は元の左保存関手の射影を保持する。
方針：引き戻し同型の第二脚の計算則を使う。
規約：元の底上の射の等式。
使われ方：分類関手の比較。 -/
lemma pairFixedRightCosliceIso_projection {C D : PresentableInfinityObject.{u}}
    (w : PrRFunctorSpace D C _⦋0⦌) :
    (pairFixedRightCosliceIso w).hom ≫ preservingRightUnitProjection w =
      pullback.snd (covariantPairUnitProjection C D) (pairFixedRightBase w) := by
  simp [pairFixedRightCosliceIso, preservingRightUnitProjection, pullback.congrHom_hom,
    Category.assoc]
  rfl

/-- 概要：元の単位族の固定右値は同じ保存条件付き coslice の分類と全自然に同型。
方針：厳密な全空間比較の同値性を同じ底上で分類する。
規約：値ごとの別の分類を選択しない。
使われ方：固定右の表現可能性を元の全族へ戻す。 -/
def pairUnitHomAtRight_cosliceIso {C D : PresentableInfinityObject.{u}}
    (w : PrRFunctorSpace D C _⦋0⦌) :
    FunctorIso (pairUnitHomAtRight w)
      (leftStraighteningInfinityDiagram (preservingRightUnitProjection w)) := by
  let p := pullback.snd (covariantPairUnitProjection C D) (pairFixedRightBase w)
  let q := preservingRightUnitProjection w
  have : LeftFibration p :=
    ⟨leftFibrations.pullback_snd _ _
      (LeftFibration.mem (p := covariantPairUnitProjection C D))⟩
  have : Quasicategory (pullback (covariantPairUnitProjection C D) (pairFixedRightBase w)) :=
    quasicategory_of_innerFibration p
  let e := pairFixedRightCosliceIso w
  have he : e.hom ≫ q = p := pairFixedRightCosliceIso_projection w
  have hf := (leftFibration_precompositionEquivalence_iff_fibers p q e.hom he).mp
    (qCatEquivalenceOfIso e).isQCatEquivalence.isPrecompositionEquivalence
  exact leftStraighteningInfinityDiagram_baseChangeIso
    (covariantPairUnitProjection C D) (pairFixedRightBase w) ≪≫
      leftClassificationComparisonIso p q e.hom he hf

/-- 概要：元の左関手は固定右の全関手 coslice の分類を表現する。
方針：後合成随伴の共変 Hom 同型と同じ coslice 分類を接続する。
規約：元の指定随伴を使う。
使われ方：保存条件を制限する前の表現可能性。 -/
def fullRightUnitRepresentationIso {C D : PresentableInfinityObject.{u}}
    {w : PrRFunctorSpace D C _⦋0⦌} {L : C.obj ⟶ D.obj}
    (a : QCatAdjunction L (rightVertexFunctor w)) :
    FunctorIso (covariantRepresentableInfinity (functorVertex L))
      (leftStraighteningInfinityDiagram (pullback.snd
        (sliceUnderProjection (SSet.yonedaEquiv.symm (functorVertex (𝟙 C.obj))))
        ((ihom C.obj).map (rightVertexFunctor w)))) := by
  have e := adjunctionCovariantHomIso (HomotopyLimits.postcompositionAdjunction a C.obj)
    (functorVertex (𝟙 C.obj))
  have hL : ((ihom C.obj).map L).app (Opposite.op ⦋0⦌) (functorVertex (𝟙 C.obj)) =
      functorVertex L := by
    change functorVertex (𝟙 C.obj ≫ L) = _
    rw [Category.id_comp]
  rw [hL] at e
  exact e ≪≫
    ((Compact.covariantRepresentableInfinity_cosliceIso (functorVertex (𝟙 C.obj))).precomp
      ((SSet.uliftFunctor.{u + 2, u + 1}).map ((ihom C.obj).map (rightVertexFunctor w)))) ≪≫
    leftStraighteningInfinityDiagram_baseChangeIso
      (sliceUnderProjection (SSet.yonedaEquiv.symm (functorVertex (𝟙 C.obj))))
      ((ihom C.obj).map (rightVertexFunctor w))

/-- 概要：指定随伴の元の左頂点は元の全単位族の固定右値を表現する。
方針：充満忠実な左包含で全関手圏の表現可能性を制限し、元の固定右分類へ戻す。
規約：全左関手の全自然変換に自然な同型。
使われ方：反変の随伴作用の充満忠実性。 -/
def pairUnitHomAtRight_representationIso {C D : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D C _⦋0⦌)
    (a : QCatAdjunction (leftVertexFunctor v) (rightVertexFunctor w)) :
    FunctorIso (covariantRepresentableInfinity v) (pairUnitHomAtRight w) := by
  let i := leftFunctorInclusion C D
  have hi : IsFullyFaithful i := isFullyFaithful_fullSubcomplexOnVertices_ι _ _
  have hv : i.app (Opposite.op ⦋0⦌) v = functorVertex (leftVertexFunctor v) :=
    ((functorVertexEquiv C.obj D.obj).apply_symm_apply v.val).symm
  have e₁ := covariantHomComparisonIso i hi v
  rw [hv] at e₁
  let p := pullback.snd
    (sliceUnderProjection (SSet.yonedaEquiv.symm (functorVertex (𝟙 C.obj))))
    ((ihom C.obj).map (rightVertexFunctor w))
  have : LeftFibration p :=
    ⟨leftFibrations.pullback_snd _ _ (LeftFibration.mem (p :=
      sliceUnderProjection (SSet.yonedaEquiv.symm (functorVertex (𝟙 C.obj)))))⟩
  exact e₁ ≪≫
    ((fullRightUnitRepresentationIso a).precomp ((SSet.uliftFunctor.{u + 2, u + 1}).map i)) ≪≫
    leftStraighteningInfinityDiagram_baseChangeIso p i ≪≫
    (pairUnitHomAtRight_cosliceIso w).symm

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
