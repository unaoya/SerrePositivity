module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.VertexComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFunctorHom
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.IntervalComposition
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.EnrichedPostcomposition

/-!
概要：固定した二つの随伴の間の自然変換を、全区間写像空間上で右 mate に送る。
方針：右随伴による前後合成を単体写像にし、単位と余単位で両端を接続する。
規約：高次単体を保持する実際の射を構成するが、その同値性は別に証明する。
使われ方：保存関手圏の core 上の随伴対応の写像空間比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Bicategory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

local instance mateHomCategory (X Y : SSet.QCat.{u}) : Category.{u} (X ⟶ Y) :=
  SSet.QCat.bicategory.homCategory X Y

/-- 概要：二つの右関手で自然変換を前後合成する単体写像。
方針：前合成の内部 Hom の作用と後合成の作用を合成する。
規約：随伴性は不要で、全自然変換と高次単体に作用する。
使われ方：右 mate の中央の比較射。 -/
def mateMiddleFunctor {C D : SSet.{u}} (R₂ R₁ : D ⟶ C) :
    (ihom C).obj D ⟶ (ihom D).obj C :=
  (pre R₂).app D ≫ (ihom D).map R₁

/-- 概要：中央の比較射の頂点は元の三つの関手の合成。
方針：内部 Hom の前後合成を頂点で計算する。
規約：ホモトピーによる同一視を使わない。
使われ方：mate の区間写像空間の両端。 -/
lemma mateMiddleFunctor_vertex {C D : SSet.{u}} (R₂ R₁ : D ⟶ C) (L : C ⟶ D) :
    (mateMiddleFunctor R₂ R₁).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex L) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((R₂ ≫ L) ≫ R₁) := by
  rfl

/-- 概要：右 mate の始端に使う単位の左 whisker。
方針：元の随伴の単位を第二の右関手で前合成する。
規約：元の h Fun の単位を保持する。
使われ方：中央の比較射の始端を R₂ に戻す。 -/
def mateUnit {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    {L₁ : C ⟶ D} {R₁ : D ⟶ C} (a₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L₁ R₁) (R₂ : D ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom R₂ ((R₂ ≫ L₁) ≫ R₁) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap R₂ ◁ a₁.unit)

/-- 概要：右 mate の終端に使う余単位の右 whisker。
方針：第二の随伴の余単位を第一の右関手で後合成する。
規約：元の h Fun の余単位を保持する。
使われ方：中央の比較射の終端を R₁ に戻す。 -/
def mateCounit {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    {L₂ : C ⟶ D} {R₂ : D ⟶ C} (a₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L₂ R₂) (R₁ : D ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom ((R₂ ≫ L₂) ≫ R₁) R₁ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv _ _ (a₂.counit ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatMap R₁)

/-- 概要：二つの随伴の間の全自然変換空間の右 mate 写像。
方針：中央の前後合成の後、元の単位と余単位で前後合成する。
規約：L₁→L₂ の変換に R₂→R₁ の変換を対応させる実際の単体写像。
使われ方：Pr の随伴対応の高次の写像空間比較。 -/
def rightMateIntervalMap {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    {L₁ L₂ : C ⟶ D} {R₁ R₂ : D ⟶ C}
    (a₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L₁ R₁) (a₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L₂ R₂) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex L₁) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex L₂) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex R₂) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex R₁) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap (mateMiddleFunctor R₂ R₁) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex L₁) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex L₂) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((R₂ ≫ L₂) ≫ R₁)) (mateUnit a₁ R₂) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPostcompose (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex R₂) (mateCounit a₂ R₁)

/-- 概要：右 mate の単体写像は任意のパラメータ族の単位・余単位の合成を表す。
方針：区間写像空間の前後合成と関手作用の族の公式を順に適用する。
規約：パラメータは任意で、quasicategory 性を要求しない。
使われ方：高次の mate の合成と両逆を同じ普遍族で検証する。 -/
lemma rightMateIntervalMap_family {A C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D]
    {L₁ L₂ : C ⟶ D} {R₁ R₂ : D ⟶ C}
    (a₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L₁ R₁) (a₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L₂ R₂)
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex L₁) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex L₂)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (f ≫ rightMateIntervalMap a₁ a₂) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap (X := (ihom D).obj C) A (mateUnit a₁ R₂) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap (mateMiddleFunctor R₂ R₁)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex L₁) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex L₂)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap (X := (ihom D).obj C) A (mateCounit a₂ R₁) := by
  simp only [rightMateIntervalMap, ← Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPostcompose_family, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose_family]

/-- 概要：h Fun の全自然変換の右 mate 全単射。
方針：双圏の conjugate 対応を元の二胞体の表示で移す。
規約：L₁→L₂ と R₂→R₁ の向きを明示する。
使われ方：単体的な mate 写像の代数的な比較。 -/
def rightMateHomEquiv {C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    {L₁ L₂ : C ⟶ D} {R₁ R₂ : D ⟶ C}
    (a₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L₁ R₁) (a₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction L₂ R₂) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom L₁ L₂ ≃ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom R₂ R₁ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv L₁ L₂).symm.trans
    ((Bicategory.conjugateEquiv a₂ a₁).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatCellEquiv R₂ R₁))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
