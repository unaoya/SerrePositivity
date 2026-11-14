module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NativeAdjointFunctorCriterion
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.RepresentableInversionLocality

/-!
表現可能前層による局所性の判定と、連続な空間値前層の表現可能性。HTT 5.5.2。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

/-- 概要：元の全前層圏では表現可能前層の反対辺の反転が Hom 局所性を検出する。
方針：F1 の元の Hom 前合成の同値判定を同じ局所性述語へ束ねる。
規約：指定端点と元の辺を保持する。
使われ方：反映された連続前層の表現対象の局所性。 -/
lemma presheaf_representableInversionDetectsLocality (A : SSet.{u}) [Quasicategory A] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RepresentableInversionDetectsLocality (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A) := by
  intro z x y e he
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.presheafInfinity_representableInversion_detects_locality z e he

/-- 概要：presentable 圏上の小余極限を小極限へ送る小さい空間値前層は表現可能。
方針：前層の反映模型で局所な表現対象を構成し、元の全同値で戻す。
規約：元の全前層そのものを全自然同型で表現する。
使われ方：余極限保存関手の全右随伴の構成。 -/
lemma presentableContinuous_isRepresentable
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C)
    (F : C.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.SendsSmallColimitsToLimits F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.IsRepresentableSmallSpaceFunctor F :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presentableContinuous_isRepresentable_of_inversionLocality
    presheaf_representableInversionDetectsLocality hC F hF

end SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.5.2.10" (partial := stronger-hyp) "仮定：presentable な始域と accessible な標的 D（Lean が強い：原典の局所小性だけより強いが、D の presentability は不要）。結論：元の F が右随伴を持つことと全小余極限保存の iff（この場合に一致）。必要な始域上の全連続前層の表現定理は presentableContinuous_isRepresentable で供給でき、未証明の比較仮定ではない。"] _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.presentableContinuous_isRepresentable
attribute [cite HTT "5.5.2.2"] _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.presentableContinuous_isRepresentable
attribute [cite HTT "5.5.2.8"] _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.presentableContinuous_isRepresentable
