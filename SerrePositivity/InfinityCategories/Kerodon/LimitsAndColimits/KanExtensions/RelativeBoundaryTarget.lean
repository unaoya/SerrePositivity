module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RelativeInternalHomLifting
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorTranspose

/-!
概要：相対境界延長の標的の充填性と転置の後合成自然性。
方針：内部 Hom の pullback の第二射影と uncurry の自然性を使う。
規約：固定するパラメータの単射性は標的の充填性には不要。
使われ方：標的図式も指定した大域的な境界延長の準備。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：inner fibration の相対内部 Hom の標的は quasicategory。
方針：第二射影は内部 Hom の後合成の底変換であり inner fibration。
規約：元と標的の圏だけが quasicategory であればよい。
使われ方：相対境界を固定する関手へ大域的な組み立てを適用する。 -/
lemma kanRelativeInternalHomTarget_quasicategory {A B D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) [InnerFibration U]
    (i : A ⟶ B) (sj : internalHom.PullbackObjObj i U) : Quasicategory sj.pt := by
  have : InnerFibration sj.snd :=
    ⟨innerFibrations.of_isPullback sj.isPullback
      (InnerFibration.mem (q := (ihom A).map U))⟩
  have : Quasicategory ((internalHom.obj (Opposite.op B)).obj E) :=
    inferInstanceAs (Quasicategory ((ihom B).obj E))
  exact quasicategory_of_innerFibration sj.snd

/-- 概要：二変数の転置は標的の後合成と可換。
方針：uncurry して二因子の交換と後合成の自然性を比較する。
規約：全ての単体集合と射は任意。
使われ方：境界の図式の U による像の指定を転置後にも保つ。 -/
lemma kanFunctorTranspose_postcomp {A B D E : SSet.{u}}
    (U : D ⟶ E) (f : A ⟶ (ihom B).obj D) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose (f ≫ (ihom B).map U) =
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose f ≫ (ihom A).map U := by
  apply uncurry_injective
  simp only [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose, uncurry_curry, uncurry_natural_right, Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
