module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.SimplicialHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ContinuousKanFilling
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ContinuousKanWeakEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalWeakEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakWhitehead
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.ContinuousKanProductUnit
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FiberProductCofinality
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredInfinity
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.TotalKanProductComparison
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanTensorAdjunction

/-!
概要：filtered な底上の fiber ごとの積の全空間 Kan 比較は弱ホモトピー同値。
方針：対角の引き戻しの cofinality と単位の直積の anodyne 性を、実際の比較の単位式で合成する。
規約：全有限試験射の連結成分による検査を弱同値の定義とは同一視しない。
使われ方：一般 coherent filtered 余極限の二項積の交換。

対応節は Kerodon 9.1（Tag 05WY）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories

/-- 概要：元の全空間の積比較と Kan 置換の単位は厳密に可換。
方針：二射影で単位式と直積射の式を比較する。
規約：二射影と単位は元のもの。使われ方：cofinal な比較から Kan 比較へ移す。 -/
lemma totalKanProductComparison_unit_product {E D B : SSet.{u}}
    (p : E ⟶ B) (q : D ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (pullback p q) ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.totalKanProductComparison p q =
      lift (pullback.fst p q) (pullback.snd p q) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app E ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app D) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.totalKanProductComparison_unit]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, tensorHom_fst, lift_fst_assoc, lift_fst]
  · simp only [Category.assoc, tensorHom_snd, lift_snd_assoc, lift_snd]

/-- 概要：filtered な底上の実際の積比較は弱ホモトピー同値。
方針：元の全空間比較の cofinality と直積の単位の弱同値性を合成し、始域の単位を消す。
規約：一般の filtered ∞ 圏上の left fibration。使われ方：一般 coherent 有限積の交換。 -/
lemma totalKanProductComparison_isWeakHomotopyEquivalence {E D B : SSet.{u}}
    [Quasicategory B] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (q : D ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.totalKanProductComparison p q) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.fiberProductToProduct_isRightCofinal p q).isWeakHomotopyEquivalence.comp
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanProductUnit_isWeakHomotopyEquivalence E D)
  rw [← totalKanProductComparison_unit_product p q] at h
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.continuousKanReplacementUnit_isWeakHomotopyEquivalence (pullback p q)).cancel_left h

/-- 概要：積比較は実際の単体的ホモトピー逆を持つ。
方針：両模型の Kan 性と証明済みの弱同値性に Whitehead の判定を使う。
規約：比較射は変更しない。使われ方：native な空間の積比較の同値。 -/
lemma totalKanProductComparison_homotopyEquivalence {E D B : SSet.{u}}
    [Quasicategory B] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (q : D ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.totalKanProductComparison p q) := by
  have := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.kanTensor_isKan
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj E) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj D)
  exact (totalKanProductComparison_isWeakHomotopyEquivalence p q).isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories
