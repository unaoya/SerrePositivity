module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndPresheafReflection
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.QCatEquivalenceAdjunction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceCalculus

/-!
概要：presentable 圏自体を前層圏の充満忠実な右随伴の像として表す。
方針：小さい compact 生成圏の Ind 反映と、元の全同値の随伴を合成する。
規約：元の圏を別の定義へ置き換えず、全関手の随伴と充満忠実性を供給する。
使われ方：小余極限の反映計算と随伴関手定理。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：presentable 圏は小さい底の前層圏の反映像となる。
方針：構成した Ind 反映を元の全同値へ合成する。
規約：反映の存在や右随伴の充満忠実性を追加入力にしない。
使われ方：元の presentable 圏での小余極限と小極限の計算。 -/
lemma IsPresentable.exists_presheafReflection {C : SSet.{u + 1}} [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C) :
    ∃ (A : SSet.{u}) (hA : Quasicategory A), letI := hA
      ∃ (L : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A ⟶ C) (R : C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A),
        Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L R) ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful R ∧ _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits L := by
  obtain ⟨κ, hκ, A, hA, ⟨r⟩, ⟨e⟩⟩ := hC.exists_reflectiveIndModel
  have := hA
  let a := r.adjunction.comp e.toAdjunction
  refine ⟨A, hA, r.reflector ≫ e.hom, e.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf κ A,
    ⟨a⟩, ?_, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.adjunction_preservesSmallColimits a⟩
  exact e.symm.isQCatEquivalence.isFullyFaithful.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf_isFullyFaithful κ A)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable export _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsPresentable (exists_presheafReflection)


/-- 概要：反映 Ind 模型の同じ全同値によって元の圏の全小余極限を構成する。
方針：前層余極限を反映してから元の圏へ輸送する。
規約：元の圏の余完備性を入力に追加しない。
使われ方：presentable の反映表示による余極限の具体的構成。 -/
lemma reflectiveIndModel_hasSmallColimits {κ : Cardinal.{u}} {A : SSet.{u}}
    [Quasicategory A] {C : SSet.{u + 1}} [Quasicategory C]
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IsIndVertex κ A))
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A) C) : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.reflectiveSubcategory_hasSmallColimits r (_root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.presheaf_hasSmallColimits A)).of_equivalence e


end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.5.1.1" (partial := direction) "仮定：presentable な準圏 C（HTT と一致）。結論：小準圏 A の前層圏からの反映表示 L⊣R と R の充満忠実性、L の全小余極限保存を構成し、R も accessible（(1)⇒(5) に一致）。(2)(3) の全 κ-small compact 余極限や (4)(6) との全ての同値はこの宣言群にない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsPresentable.exists_presheafReflection
