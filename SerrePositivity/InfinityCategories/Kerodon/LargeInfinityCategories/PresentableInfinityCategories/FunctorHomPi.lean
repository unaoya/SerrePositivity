module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorPiIso
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorHomWhiskering
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceFullyFaithful

/-!
概要：小さい全直積に値を取る全関手間の二胞体を全成分へ分解する。
方針：関手圏の厳密な積比較とホモトピー圏の全 Hom 比較を合成する。
規約：任意の全パラメーターを保持する。
使われ方：小さい族の全随伴の単位と三角恒等式。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：直積値の全関手間の元の二胞体は全成分の二胞体の族と全単射。
方針：全関手圏の厳密な同型の充満忠実性と全直積の Hom 比較を使う。
規約：指定した元の両全関手を保持する。
使われ方：直積の全随伴の構成。 -/
def functorHomPiEquiv {ι : Type u} {T : SSet.{u + 1}} {C : ι → SSet.{u + 1}}
    [∀ i, Quasicategory (C i)] (F G : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet C) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G ≃ ∀ i, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i) (G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorPiIso T C
  have hf := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e).isQCatEquivalence.isFullyFaithful.toHoFullyFaithful
  exact hf.homEquiv.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetHoHomEquiv _ _)

/-- 概要：全二胞体の成分比較は元の各射影による後合成。
方針：元の二胞体の一本の辺の代表で計算する。
規約：全パラメーターを保持する。使われ方：全自然性と合成の検証。 -/
lemma functorHomPiEquiv_apply {ι : Type u} {T : SSet.{u + 1}}
    {C : ι → SSet.{u + 1}} [∀ i, Quasicategory (C i)]
    {F G : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet C} (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G) (i : ι) :
    functorHomPiEquiv F G α i =
      (hoFunctor.map ((ihom T).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i))).toFunctor.map α := by
  obtain ⟨e, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ α
  rfl

/-- 概要：元の全二胞体の合成は全成分で計算される。
方針：各後合成関手の合成保存を使う。
規約：全関手を保持する。使われ方：直積の三角恒等式。 -/
lemma functorHomPiEquiv_comp {ι : Type u} {T : SSet.{u + 1}}
    {C : ι → SSet.{u + 1}} [∀ i, Quasicategory (C i)]
    {F G H : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet C} (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G) (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom G H) (i : ι) :
    functorHomPiEquiv F H (α ≫ β) i =
      functorHomPiEquiv F G α i ≫ functorHomPiEquiv G H β i := by
  simp only [functorHomPiEquiv_apply, CategoryTheory.Functor.map_comp]

/-- 概要：恒等二胞体の全成分は元の恒等二胞体。
方針：各後合成関手の恒等保存を使う。
規約：元の全関手 F。使われ方：全同型の逆条件。 -/
lemma functorHomPiEquiv_id {ι : Type u} {T : SSet.{u + 1}}
    {C : ι → SSet.{u + 1}} [∀ i, Quasicategory (C i)]
    (F : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet C) (i : ι) : functorHomPiEquiv F F (𝟙 _) i = 𝟙 _ := by
  simp only [functorHomPiEquiv_apply, CategoryTheory.Functor.map_id]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
