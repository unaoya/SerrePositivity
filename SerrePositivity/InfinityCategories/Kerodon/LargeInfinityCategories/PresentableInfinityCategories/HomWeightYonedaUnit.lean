module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.EndSectionsYonedaModel
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HomComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowFunctorComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HomWeightJointClassificationHom

/-!
概要：任意の元の関手から、Yoneda と元の Hom 係数前層族の間の指定単位を構成する。
方針：twisted arrow の実際の比較を分類し、共同 Hom の全比較を curry する。
規約：充満忠実性は仮定しない。指定単位の左 Kan 普遍性は別工程。
使われ方：P-12 の Yoneda 模型に現れる全自然変換空間の普遍性の入力。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


local instance supplyHomWeightYonedaUnit_productQuasicategory
    {A : SSet.{u}} [Quasicategory A] : Quasicategory (A.op ⊗ A) :=
  quasicategory_of_innerFibration (CartesianMonoidalCategory.fst A.op A)

/-- 概要：全共同図式間の射を curry した全図式間の射へ移す。
方針：関手空間の curry の Hom 作用を元の両頂点へ輸送する。
規約：射の可逆性を要求しない。使われ方：元の共同 Hom の比較から指定単位を作る。 -/
def curryFunctorHom {A B X : SSet.{u}} {f g : A ⊗ B ⟶ X}
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (curry f) (curry g) := by
  have h := (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap A B X)).toFunctor.map α
  change (HomotopyCategory.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap A B X).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) : hoFunctor.obj ((ihom B).obj ((ihom A).obj X))) ⟶
    HomotopyCategory.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap A B X).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g)) at h
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorSpaceCurryMap_vertex] using h

/-- 概要：任意の元の関手の全共同 Hom 比較を元の二変数図式の射にする。
方針：元の twisted arrow 比較を分類して、直積の宇宙比較に沿って制限する。
規約：元の全図式を使い、充満忠実性を仮定しない。
使われ方：元の Yoneda と Hom 係数前層族の指定単位の構成。 -/
def functorHomBifunctorUnit {A C : SSet.{u}} [Quasicategory A] [Quasicategory C]
    (F : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.homInfinityJointEvaluation A)
      ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso A.op A).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomBifunctorDiagram F F) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomBifunctorProjection F F) := inferInstance
  let α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.twistedArrowHomInfinity A) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomBifunctorDiagram F F) :=
    homWeightJointClassificationHom F
  exact (hoFunctor.map ((pre (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso A.op A).inv).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})).toFunctor.map α

/-- 概要：任意の元の関手の Yoneda から、元の Hom 係数族の制限への指定単位。
方針：共同 Hom の全比較を curry し、元の両全図式の表示へ正規化する。
規約：単位の可逆性や左 Kan 普遍性を仮定しない。
使われ方：end 比較を元の関手の左 Kan 普遍性として表すための実単位。 -/
def homWeightYonedaUnit {A C : SSet.{u}} [Quasicategory A] [Quasicategory C]
    (F : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A)
      ((SSet.uliftFunctor.{u + 1, u}).map F ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafHomWeightDiagram F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomBifunctorDiagram_curry F F)
    (curryFunctorHom (functorHomBifunctorUnit F))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
