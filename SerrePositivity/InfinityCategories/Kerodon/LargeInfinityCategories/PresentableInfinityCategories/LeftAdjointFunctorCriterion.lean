module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ReflectiveContinuousDescent
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RightAdjointFromContravariantModels

/-!
概要：指定した二つの比較界面を使い、presentable 圏の左随伴関手を判定する。
方針：連続前層の表現可能性を反映模型で構成し、反変 Hom 模型から全右随伴を組み立てる。
規約：Yoneda 辺作用の局所性比較と指定宇宙変更の充満忠実性を明示する。
使われ方：依頼済みの比較界面から HTT 5.5.2.9 の余極限保存側へ接続する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：二つの比較界面の下で presentable 圏の左随伴は小余極限保存と同値。
方針：反映による連続前層の表現定理を、右随伴の構成へ入力する。
規約：比較界面の存在は主張せず、元の全関手の全随伴を結論する。
使われ方：F1 と Compact の供給後の d4 の最終接続。 -/
lemma exists_rightAdjoint_iff_preservesSmallColimits_of_comparisonInterfaces
    (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseDiagram.{u})
    (hLocal : ∀ (A : SSet.{u}) [Quasicategory A],
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.RepresentableInversionDetectsLocality (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A))
    {C D : SSet.{u + 1}} [Quasicategory C] [Quasicategory D]
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C) (hD : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable D) (L : C ⟶ D) :
    (∃ R : D ⟶ C, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R)) ↔ _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits L :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_rightAdjoint_iff_preservesSmallColimits_of_representability hU hD.isAccessible
    (fun F hF ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presentableContinuous_isRepresentable_of_inversionLocality hLocal hC F hF) L

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
