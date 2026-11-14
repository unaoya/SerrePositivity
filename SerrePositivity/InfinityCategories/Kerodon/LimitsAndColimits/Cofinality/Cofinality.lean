module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalFunctorSpace
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.InitialCofinality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：左右 cofinal な単体集合の射と、始対象の包含による left cofinality。
方針：left/right fibration への相対関手空間の制限が実際のホモトピー逆を持つと要求する。
規約：right は余極限、left は極限の向き。始域・標的の quasicategory 性や単射性は不要。
使われ方：Kerodon Definition 7.2.1.1（Tag 02N1）、Proposition 7.2.1.3（Tag 02N3）、HTT §4.1。
Quillen A の弱可縮な coslice による判定は後続工程で証明する。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：left cofinal な射の相対関手空間による定義。
方針：任意の left fibration への底上の関手の制限にホモトピー逆の存在を要求する。
規約：標的の宇宙と同じ宇宙の fibration で検査する。充填性は p だけに課す。
使われ方：Kerodon Definition 7.2.1.1（Tag 02N1）、極限を計算する向き。 -/
@[kerodon 02N1]
def IsLeftCofinal {A B : SSet.{u}} (i : A ⟶ B) : Prop :=
  ∀ (E : SSet.{u}) (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p],
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorPre p (𝟙 B) i)

/-- 概要：right cofinal な射の相対関手空間による定義。
方針：任意の right fibration への底上の関手の制限にホモトピー逆の存在を要求する。
規約：left の opposite による略記にはせず、元の底上の制限写像を指定する。
使われ方：Kerodon Definition 7.2.1.1（Tag 02N1）、余極限を計算する向き。 -/
@[kerodon 02N1]
def IsRightCofinal {A B : SSet.{u}} (i : A ⟶ B) : Prop :=
  ∀ (E : SSet.{u}) (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p],
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorPre p (𝟙 B) i)

/-- 概要：恒等射は left cofinal。
方針：相対前合成の恒等則と恒等射のホモトピー逆を使う。
規約：底は任意の単体集合。
使われ方：Kerodon §7.2.1（Tag 02N0）、cofinality の基本例。 -/
lemma isLeftCofinal_id (B : SSet.{u}) : IsLeftCofinal (𝟙 B) := by
  intro E p hp
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorPre_id]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isSimplicialHomotopyEquivalence_id _

/-- 概要：恒等射は right cofinal。
方針：相対前合成の恒等則と恒等射のホモトピー逆を使う。
規約：right fibration の全空間の quasicategory 性も不要。
使われ方：Kerodon §7.2.1（Tag 02N0）、cofinality の基本例。 -/
lemma isRightCofinal_id (B : SSet.{u}) : IsRightCofinal (𝟙 B) := by
  intro E p hp
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorPre_id]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isSimplicialHomotopyEquivalence_id _

/-- 概要：left anodyne な射に沿う任意の固定図式の制限はホモトピー同値。
方針：相対関手の制限の trivial Kan fibration 性と、その両端の Kan 性を使う。
規約：底の図式 a は恒等に限らず、任意の射。
使われ方：Kerodon Proposition 7.2.1.3（Tag 02N3）、始対象でのパラメータ付き制限。 -/
lemma cofinalFunctorPre_isSimplicialHomotopyEquivalence_of_leftAnodyne
    {A D E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (a : A ⟶ B) (i : D ⟶ A) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorPre p a i) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorPre_trivialKanFibration p a i hi
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _).isSimplicialHomotopyEquivalence

/-- 概要：left anodyne な射は left cofinal。
方針：任意の left fibration と恒等底図式に対して制限のホモトピー逆を得る。
規約：射の単射性を別の仮定として加えない。
使われ方：Kerodon Proposition 7.2.1.3（Tag 02N3） の十分性。 -/
lemma isLeftCofinal_of_leftAnodyne {A B : SSet.{u}} (i : A ⟶ B)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i) : IsLeftCofinal i := by
  intro E p hp
  exact cofinalFunctorPre_isSimplicialHomotopyEquivalence_of_leftAnodyne p (𝟙 B) i hi

/-- 概要：通常の圏の始対象の頂点包含は left cofinal。
方針：A2h の nervePoint_leftAnodyne を一般の left cofinality に接続する。
規約：対象と射の宇宙は独立で、nerve は max v w に置く。
使われ方：Kerodon Example 7.2.1.4（Tag 03LQ）、A2h の始対象による極限計算の向きの確認。 -/
lemma nervePoint_isLeftCofinal {I : Type v} [Category.{w} I] {c : I}
    (hc : IsInitial c) : IsLeftCofinal (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint c) :=
  isLeftCofinal_of_leftAnodyne _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint_leftAnodyne hc)

/-- 概要：始対象への slice 制限は quasicategory の同値。
方針：A2h の同じ制限写像の trivial Kan fibration 性から明示的な逆データを得る。
規約：これは left cofinal な始対象の包含による極限計算であり、right の主張ではない。
使われ方：HTT §4.1.1、Kerodon §7.2.2（Tag 02NQ）、既存 initialCofinality との接続。 -/
lemma initialRestriction_isQCatEquivalence {I : Type v} [Category.{w} I] {c : I}
    (hc : IsInitial c) {X : SSet.{max v w}} [Quasicategory X] (F : nerve I ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialRestriction F c) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.initialCofinality hc F
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "4.1.1.1"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal
