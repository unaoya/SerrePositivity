module

public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.AdjointRepresentability

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NativeAdjointFunctorCriterion
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.RepresentableInversionLocality
public import Mathlib.Tactic.CrossRefAttribute

/-!
presentable ∞ 圏の関手について、右随伴の存在と小余極限保存を比較する。Kerodon 9.5.2.1（Tag 06Q5）。HTT 5.5.2.9。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：presentable 圏の関手が右随伴を持つことは全小余極限保存と同値。
方針：小さい反変 Hom 合成を表現し、元の全随伴を構成する。
規約：比較界面や一般局所化の存在を追加入力にしない。
使われ方：HTT 5.5.2.9、Pr^L の随伴による特徴づけ。 -/
@[kerodon 06Q5]
lemma exists_rightAdjoint_iff_preservesSmallColimits
    {C D : SSet.{u + 1}} [Quasicategory C] [Quasicategory D]
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C) (hD : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable D) (L : C ⟶ D) :
    (∃ R : D ⟶ C, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R)) ↔ _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits L :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_rightAdjoint_iff_preservesSmallColimits_of_inversionLocality
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.presheaf_representableInversionDetectsLocality hC hD L

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
