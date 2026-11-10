module

public import SerrePositivity.InfinityCategories.F1B.Adjunction.AdjunctionMappingSpaces
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.RightIntervalEquivalence
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：随伴から右 pinched 写像空間のホモトピー同値を構成する。
方針：右模型と区間模型の同値を、区間模型の adjunct 比較の前後で合成する。
規約：対象変数の射に関する自然性と特徴づけの逆向きは別途証明する。
使われ方：Kerodon Prop 6.2.1.17、HTT §5.2 の随伴の写像空間の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.QCatAdjunction

/-- 概要：区間模型での adjunct 比較を明示的な同値のデータにする。
方針：実際のホモトピー逆から Kan 複体間の同値を取り出す。
規約：順方向の射は intervalMap そのもの。
使われ方：pinched 模型との前後の合成。 -/
noncomputable def intervalMappingEquivalence {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : QCatAdjunction F G) (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    QCatEquivalence (intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y)
      (intervalMappingSpace x (G.app (Opposite.op ⦋0⦌) y)) :=
  (a.intervalMap_isSimplicialHomotopyEquivalence x y).isQCatEquivalence.choose

/-- 概要：随伴が与える右 pinched 写像空間の同値。
方針：右模型→区間模型→adjunct 比較→右模型の三つの同値を合成する。
規約：各点での同値のデータ。対象変数の射に関する自然性はここでは主張しない。
使われ方：Kerodon Prop 6.2.1.17 の順方向の pinched 模型版。 -/
@[kerodon 02F1]
noncomputable def pinchedHomEquivalence {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : QCatAdjunction F G) (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    QCatEquivalence (pinchedHom (F.app (Opposite.op ⦋0⦌) x) y)
      (pinchedHom x (G.app (Opposite.op ⦋0⦌) y)) :=
  (SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace_isQCatEquivalence (F.app (Opposite.op ⦋0⦌) x) y).choose.trans
    ((a.intervalMappingEquivalence x y).trans
      (SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace_isQCatEquivalence x (G.app (Opposite.op ⦋0⦌) y)).choose.symm)

/-- 概要：右 pinched 模型の adjunct 比較の順方向の射。
方針：明示的な同値の hom を取る。
規約：区間模型の比較と相対 join 延長で選んだ逆を使う。
使われ方：写像空間の比較の自然性を述べる指定射。 -/
noncomputable def pinchedMap {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G) (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    pinchedHom (F.app (Opposite.op ⦋0⦌) x) y ⟶ pinchedHom x (G.app (Opposite.op ⦋0⦌) y) :=
  (a.pinchedHomEquivalence x y).hom

/-- 概要：右 pinched 模型の比較射は実際の単体的ホモトピー逆を持つ。
方針：Kan 複体間の同値のデータから実際のホモトピー逆へ戻す。
規約：π₀ の全単射だけへの弱化ではない。
使われ方：Kerodon Prop 6.2.1.17 の写像空間のホモトピー同値。 -/
lemma pinchedMap_isSimplicialHomotopyEquivalence {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : QCatAdjunction F G) (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (a.pinchedMap x y) :=
  (a.pinchedHomEquivalence x y).isQCatEquivalence.isSimplicialHomotopyEquivalence

/-- 概要：pinched の比較射は区間模型の adjunct 比較と h Fun の同型で整合する。
方針：終域側の模型比較の余単位を前合成する。
規約：同値に使った同じ比較射・逆のデータを使う。
使われ方：右模型の比較が単位による adjunct を表すことの接続。 -/
noncomputable def pinchedMap_comparisonIso {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : QCatAdjunction F G) (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    FunctorIso (a.pinchedMap x y ≫ SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace x (G.app (Opposite.op ⦋0⦌) y))
      (SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y ≫ a.intervalMap x y) := by
  simpa only [pinchedMap, pinchedHomEquivalence, intervalMappingEquivalence,
    QCatEquivalence.trans, QCatEquivalence.symm, IsQCatEquivalence.choose,
    Category.assoc, Category.comp_id] using
    FunctorIso.precomp
      (SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace_isQCatEquivalence x (G.app (Opposite.op ⦋0⦌) y)).choose.invHomIso
      (SerrePositivity.InfinityCategories.pinchedHomToIntervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y ≫ a.intervalMap x y)

end SerrePositivity.InfinityCategories.QCatAdjunction
