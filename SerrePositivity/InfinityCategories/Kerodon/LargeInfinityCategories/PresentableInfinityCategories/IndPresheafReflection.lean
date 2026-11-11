module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndReflectorAdjunction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ReflectionSmallColimits
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ReflectionSmallLimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableEquivalence

/-!
概要：余完備な Ind 模型を全前層圏の反映全部分圏として構成する。
方針：Yoneda 左 Kan 延長の随伴を反映に束ね、局所対象の極限閉性を適用する。
規約：任意の Ind の余完備性は仮定として明示し、presentable 模型では元の全同値から供給する。
使われ方：presentable 圏の小極限と具体的な前層反映模型。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：余完備な Ind 模型には全前層圏からの反映が存在する。
方針：構成した同じ Yoneda 左 Kan 延長と包含の随伴を保持する。
規約：一般 Bousfield 局所化の存在は使わない。
使われ方：反映による余極限計算と極限の存在。 -/
def indPresheafReflection {κ : Cardinal.{u}} [Fact κ.IsRegular]
    {A : SSet.{u}} [Quasicategory A] (h : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IsIndVertex κ A) := by
  let hex := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ind_exists_presheafReflector h
  exact ⟨hex.choose, Classical.choice hex.choose_spec⟩

/-- 概要：余完備な Ind 模型は全小極限も持つ。
方針：前層の完備性と反映像の同型閉性を使う。
規約：Ind の交換定理を追加の入力にしない。
使われ方：presentable の完備性。 -/
lemma ind_hasSmallLimits_of_hasSmallColimits {κ : Cardinal.{u}} [Fact κ.IsRegular]
    {A : SSet.{u}} [Quasicategory A] (h : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A)) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallLimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.reflectiveSubcategory_hasSmallLimits (indPresheafReflection h)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isIndVertex_isoClosed κ A) (_root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.presheaf_hasSmallLimits A)

/-- 概要：presentable 圏は前層の反映された小さい Ind 模型と同値。
方針：元の compact 生成圏の Ind 同値で余完備性を回収し、専用反映を作る。
規約：反映の存在や Ind の余完備性を追加入力にしない。
使われ方：元の presentable 圏の極限・余極限構成。 -/
lemma IsPresentable.exists_reflectiveIndModel {C : SSet.{u + 1}} [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C) :
    ∃ (κ : Cardinal.{u}), κ.IsRegular ∧ ∃ (A : SSet.{u}) (hA : Quasicategory A),
      have := hA
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IsIndVertex κ A)) ∧
        Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A) C) := by
  obtain ⟨κ, hκ, A, hA, hcolim, he⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isPresentable_iff_cocompleteIndEquivalence C).mp hC
  have := hA
  have : Fact κ.IsRegular := ⟨hκ⟩
  exact ⟨κ, hκ, A, hA, ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.indPresheafReflection hcolim⟩, he⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable export _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsPresentable (exists_reflectiveIndModel)


end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
