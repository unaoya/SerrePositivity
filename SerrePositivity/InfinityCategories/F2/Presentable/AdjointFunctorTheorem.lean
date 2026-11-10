module

public import SerrePositivity.InfinityCategories.F2.Presentable.NativeAdjointFunctorCriterion
public import SerrePositivity.InfinityCategories.F1.Yoneda.RepresentableInversionLocality
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：presentable 圏の連続前層の表現可能性と随伴関手定理を無条件に接続する。
方針：元の表現可能前層の辺作用による局所性判定を反映移送へ入力する。
規約：宇宙比較・局所性・随伴の存在を追加入力にしない。
使われ方：HTT 5.5.2.9 と Pr^L／Pr^R の随伴による対応。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：元の全前層圏では表現可能前層の反対辺の反転が Hom 局所性を検出する。
方針：F1 の元の Hom 前合成の同値判定を同じ局所性述語へ束ねる。
規約：指定端点と元の辺を保持する。
使われ方：反映された連続前層の表現対象の局所性。 -/
lemma presheaf_representableInversionDetectsLocality (A : SSet.{u}) [Quasicategory A] :
    RepresentableInversionDetectsLocality (PresheafInfinity A) := by
  intro z x y e he
  exact presheafInfinity_representableInversion_detects_locality z e he

/-- 概要：presentable 圏上の小余極限を小極限へ送る小さい空間値前層は表現可能。
方針：前層の反映模型で局所な表現対象を構成し、元の全同値で戻す。
規約：元の全前層そのものを全自然同型で表現する。
使われ方：余極限保存関手の全右随伴の構成。 -/
lemma presentableContinuous_isRepresentable
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C)
    (F : C.op ⟶ SpaceInfinity.{u}) (hF : SendsSmallColimitsToLimits F) :
    IsRepresentableSmallSpaceFunctor F :=
  presentableContinuous_isRepresentable_of_inversionLocality
    presheaf_representableInversionDetectsLocality hC F hF

/-- 概要：presentable 圏の関手が右随伴を持つことは全小余極限保存と同値。
方針：小さい反変 Hom 合成を表現し、元の全随伴を構成する。
規約：比較界面や一般局所化の存在を追加入力にしない。
使われ方：HTT 5.5.2.9、Pr^L の随伴による特徴づけ。 -/
@[kerodon 06Q5]
lemma exists_rightAdjoint_iff_preservesSmallColimits
    {C D : SSet.{u + 1}} [Quasicategory C] [Quasicategory D]
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C) (hD : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable D) (L : C ⟶ D) :
    (∃ R : D ⟶ C, Nonempty (QCatAdjunction L R)) ↔ _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits L :=
  exists_rightAdjoint_iff_preservesSmallColimits_of_inversionLocality
    presheaf_representableInversionDetectsLocality hC hD L

end SerrePositivity.InfinityCategories.F2.Presentable
