module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrecompositionUnit
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FlipFunctorHomComposition
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FlipConstantFunctorHom

/-!
概要：前合成の Hom 対応に必要な、転置の合成保存と二つの前合成自然性。
方針：内部 Hom の交換の自然性を h の元の射へ写し、端点の輸送を相殺する。
規約：P のコミット済みの変数交換の公開界面のみを使う。
使われ方：全パラメータの自然な Hom 対応から前合成の全 QCat 随伴を構成する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：元の Hom の転置は合成を保つ。
方針：コミット済みの変数交換による Hom 同値の合成保存を使う。
規約：元の三つの関手を保持する。
使われ方：前合成の随伴の Hom 対応の自然性。 -/
lemma transposeHomEquiv_comp {A B Z : SSet.{u}} [Quasicategory Z]
    {U V W : A ⟶ (ihom B).obj Z} (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V) (β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom V W) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposeHomEquiv U W (α ≫ β) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposeHomEquiv U V α ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposeHomEquiv V W β :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.flipFunctorHomEquiv_comp α β

/-- 概要：関手の始域の前合成による Hom の像は、転置後のパラメータ前合成に一致する。
方針：交換と第二始域への前合成の自然性を h に写し、端点の等式を相殺する。
規約：任意のパラメータ A と任意の二つの関手間の射を扱う。
使われ方：前合成の随伴の両変数の自然性。 -/
lemma transposeHomEquiv_pre_right {A B₀ B Z : SSet.{u}} [Quasicategory Z]
    (j : B₀ ⟶ B) {U V : A ⟶ (ihom B).obj Z} (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr (A := B₀) (D := (ihom A).obj Z)
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_right j U) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_right j V)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposeHomEquiv (A := A) (B := B₀) (Z := Z) (U ≫ (pre j).app Z) (V ≫ (pre j).app Z)
        ((hoFunctor.map ((ihom A).map ((pre j).app Z))).toFunctor.map
          (X := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U))
          (Y := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V)) α)) =
    (hoFunctor.map ((pre j).app ((ihom A).obj Z))).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposeHomEquiv U V α) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr (A := B₀) (D := (ihom A).obj Z) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_right j U)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_right j V)
    ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso A B₀ Z).hom).toFunctor.map
      ((hoFunctor.map ((ihom A).map ((pre j).app Z))).toFunctor.map
          (X := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U))
          (Y := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex V)) α)) = _
  have h := CategoryTheory.Functor.congr_hom
    (congrArg (fun f ↦ (hoFunctor.map f).toFunctor) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso_pre (A := A) (X := Z) j)) α
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.hoFunctor_map_comp_apply] at h
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr, Iso.homCongr_apply, eqToIso.inv, eqToIso.hom]
  rw [h]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp, Category.comp_id]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.hoFunctor_map_comp_apply _ _ _

/-- 概要：パラメータ前合成による Hom の像は、転置後の関手の後合成に一致する。
方針：交換と第一始域への前合成の自然性を h に写し、端点の等式を相殺する。
規約：任意のパラメータの射と元の Hom を保持する。
使われ方：前合成の随伴の全パラメータ自然性。 -/
lemma transposeHomEquiv_pre_left {A₀ A B Z : SSet.{u}} [Quasicategory Z]
    (i : A₀ ⟶ A) {U V : A ⟶ (ihom B).obj Z} (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom U V) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr (A := B) (D := (ihom A₀).obj Z)
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_left i U) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_left i V)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposeHomEquiv (i ≫ U) (i ≫ V)
        ((hoFunctor.map ((pre i).app ((ihom B).obj Z))).toFunctor.map α)) =
    (hoFunctor.map ((ihom B).map ((pre i).app Z))).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.transposeHomEquiv U V α) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr (A := B) (D := (ihom A₀).obj Z) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_left i U)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_left i V)
    ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso A₀ B Z).hom).toFunctor.map
      ((hoFunctor.map ((pre i).app ((ihom B).obj Z))).toFunctor.map α)) = _
  have h := CategoryTheory.Functor.congr_hom
    (congrArg (fun f ↦ (hoFunctor.map f).toFunctor) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.internalHomSwap_pre_left i B Z)) α
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.hoFunctor_map_comp_apply] at h
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr, Iso.homCongr_apply, eqToIso.inv, eqToIso.hom]
  rw [h]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp, Category.comp_id]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.hoFunctor_map_comp_apply _ _ _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
