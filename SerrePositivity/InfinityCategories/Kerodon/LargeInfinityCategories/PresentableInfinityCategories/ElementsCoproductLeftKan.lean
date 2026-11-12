module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ElementsDegreeFiber
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.CofinalColimitExistence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.CoproductRealizationConditions
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.LeftKanShapeIso
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.UniverseLeftKanShape
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.CofinalUniverseLift
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftCommaCoconeColimit

/-!
概要：小余積を持つ標的への要素圏の次数射影に沿う全左 Kan 延長。
方針：各局所添字を同じ離散ファイバーへ cofinal に縮約する。
規約：標的に全小余極限や前層表示を仮定しない。
使われ方：小余積と幾何学的実現から小余極限を構成する一般 bar 図式。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {I : Type u} [Category.{u} I] (Y : I ⥤ Type u)

/-- 概要：同じ次数の離散ファイバーから持ち上げた元の左 Kan 添字への比較。
方針：通常の comma の nerve 比較と元の宇宙同型を合成する。
規約：元の指定次数を保持する。
使われ方：標的の小余積だけによる各局所余極限の存在。 -/
def elementsCoproductKanComparison (i : I) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve (Discrete (Y.obj i))) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (Functor.Elements.π Y)))
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)) :=
  (SSet.uliftFunctor.{u + 1, u}).map
    (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.elementsDegreeFiber Y i) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeIso (Functor.Elements.π Y) i).hom) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.leftKanShapeUniverseIso (nerveMap (Functor.Elements.π Y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)).hom

/-- 概要：同じ離散次数ファイバーによる元の局所添字の比較は right cofinal。
方針：明示的な comma の左随伴、nerve 同型、宇宙同型を合成する。
規約：小さい次数を別の同値類へ取り替えない。
使われ方：局所左 Kan 図式の余極限の存在を小余積から戻す。 -/
lemma elementsCoproductKanComparison_isRightCofinal (i : I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (elementsCoproductKanComparison Y i) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isRightCofinal_ulift _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.elementsDegreeFiber_nerve_isRightCofinal Y i).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_isIso
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeIso (Functor.Elements.π Y) i).hom))).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_isIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.leftKanShapeUniverseIso (nerveMap (Functor.Elements.π Y))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)).hom)

/-- 概要：小余積を持つ標的では、元の次数射影の全局所左 Kan 図式が余極限を持つ。
方針：離散ファイバーの小余積を構成し、同じ cofinal 比較で存在を戻す。
規約：元の図式は任意で、標的を前層圏に限定しない。
使われ方：次数ごとの小余積の coherent な全選択。 -/
lemma elementsCoproduct_leftKanDiagram_hasColimit
    {X : SSet.{u + 1}} [Quasicategory X] (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HasSmallCoproducts X)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve Y.Elements) ⟶ X)
    (v : ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (Functor.Elements.π Y))) F v) := by
  rcases v with ⟨v⟩
  obtain ⟨i, rfl⟩ := nerveEquiv.symm.surjective v
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.hasColimit_of_rightCofinalRestriction (elementsCoproductKanComparison Y i)
    (elementsCoproductKanComparison_isRightCofinal Y i)
  exact hX (Y.obj i) _

/-- 概要：小余積だけから、要素圏の次数射影に沿う全左 Kan 延長が存在する。
方針：全局所余極限の存在を元の左 Kan 存在定理へ渡す。
規約：全ての次数の自然性を持つ単位を得る。
使われ方：小余積からの一般の単体的 bar 図式の構成。 -/
lemma elementsCoproduct_exists_leftKanExtension
    {X : SSet.{u + 1}} [Quasicategory X] (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HasSmallCoproducts X)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve Y.Elements) ⟶ X) :
    ∃ (G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ X)
      (β : SSet.Homotopy F
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (Functor.Elements.π Y)) ≫ G)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsLeftKanExtension
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (Functor.Elements.π Y))) F G β :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanLeftExtension_of_local_colimits _ F
    (elementsCoproduct_leftKanDiagram_hasColimit Y hX F)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
