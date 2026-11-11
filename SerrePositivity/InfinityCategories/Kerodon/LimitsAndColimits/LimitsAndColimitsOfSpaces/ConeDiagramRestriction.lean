module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FixedEndpointConeIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.SectionConeUniversal
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.UniversalScaffoldEvaluation

/-!
概要：両端固定の錐と coslice の切断を、図式の射に沿って制限する。
方針：内部 Hom の前合成を両端の fiber に制限し、普遍族の展開で比較する。
規約：任意の単体集合の図式を扱い、頂点 x は共通に固定する。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6（Tag 05QS） の切断の制限による極限判定。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 概要：両端固定の錐の関手空間への包含。
方針：定義に使った fiber の包含に名前を与える。
規約：両端の図式は x と p。
使われ方：Kerodon 4.6.6.8（Tag 04J5） の制限射の値の検査。 -/
abbrev endpointConeEvaluation {K X : SSet.{u}} (p : K ⟶ X) (x : X _⦋0⦌) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInclusion (Δ[0] : SSet.{u}) K)).app X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (SSet.yonedaEquiv.symm x) p))

/-- 概要：join の前合成は両端固定の錐を引き戻した図式の両端固定の錐へ写す。
方針：左右の制限で fiber の固定条件を検査する。
規約：図式の射 f に単射性は不要。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の共通模型の制限射の構成。 -/
lemma endpointConeEvaluation_restrict_fixed {K J X : SSet.{u}} (p : J ⟶ X)
    (x : X _⦋0⦌) (f : K ⟶ J) :
    endpointConeEvaluation p x ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) f)).app X ≫
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInclusion Δ[0] K)).app X =
        SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (SSet.yonedaEquiv.symm x) (f ≫ p))) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointFunctor_hom_ext
  · rw [Category.assoc, Category.assoc, ← NatTrans.comp_app, ← pre_map,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl_inclusion, ← NatTrans.comp_app, ← pre_map,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointConeSpace_inl, SSet.const_comp]
    rfl
  · rw [Category.assoc, Category.assoc, ← NatTrans.comp_app, ← pre_map,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr_inclusion, ← NatTrans.comp_app, ← pre_map, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap,
      pre_map, NatTrans.comp_app, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointConeSpace_inr,
      SSet.const_comp]
    rfl

/-- 概要：両端固定の錐を図式の射に沿って制限する。
方針：join の右因子への前合成を固定条件で持ち上げる。
規約：充填性や同値性を仮定しない実際の射。
使われ方：HTT 4.2.4.1 の共通模型での制限の比較。 -/
def endpointConeRestrict {K J X : SSet.{u}} (p : J ⟶ X) (x : X _⦋0⦌) (f : K ⟶ J) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointConeSpace p x ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointConeSpace (f ≫ p) x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _
    (endpointConeEvaluation p x ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) f)).app X)
    (endpointConeEvaluation_restrict_fixed p x f)

/-- 概要：両端固定の錐の制限の包含後の値は join の前合成。
方針：fiber の持ち上げの計算則を使う。
規約：全次数での厳密な等式。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の制限の可換四角形。 -/
lemma endpointConeRestrict_evaluation {K J X : SSet.{u}} (p : J ⟶ X)
    (x : X _⦋0⦌) (f : K ⟶ J) :
    endpointConeRestrict p x f ≫ endpointConeEvaluation (f ≫ p) x =
      endpointConeEvaluation p x ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) f)).app X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _

/-- 概要：切断の族を図式で制限して展開すると右因子の前合成になる。
方針：相対関手の前合成と coslice の uncurry の自然性を使う。
規約：全パラメータ A について成立する。
使われ方：Kerodon 7.4.1.6（Tag 05QS） の切断模型の制限の計算。 -/
lemma sectionConeUncurry_restrict {A K J X : SSet.{u}} {p : J ⟶ X}
    {x : X _⦋0⦌} (s : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coherentConeSectionSpace p x) (f : K ⟶ J) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sectionConeUncurry (s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) p f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (f ▷ A) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sectionConeUncurry s := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.sectionConeUncurry
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorUncurry_pre, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
