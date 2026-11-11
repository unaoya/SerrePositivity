module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingArrowUnitComparison
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingAdjunction

/-!
概要：各点で同値な coherent な矢印比較から随伴を構成する。
方針：恒等矢印から単位を抽出し、標準比較とのホモトピーを経由して局所判定を使う。
規約：入力には単位・余単位・全パラメータの全単射を要求しない。
使われ方：B1 の自然な写像空間対応から随伴への逆方向の具体的な比較模型。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
namespace MappingArrowComparison
variable {X Y : SSet.{u}} {F : X ⟶ Y} {G : Y ⟶ X}
variable (q : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingArrowComparison F G)

/-- 概要：coherent な矢印比較が各点でホモトピー同値である条件。
方針：各点の区間写像空間への制限に実際のホモトピー逆を要求する。
規約：単位は入力に含めず、全パラメータの同値条件にも強めない。
使われ方：coherent な比較から随伴を構成する際の唯一の局所条件。 -/
def IsPointwiseEquivalence : Prop :=
  ∀ (x : X _⦋0⦌) (y : Y _⦋0⦌), _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (q.intervalMap x y)

/-- 概要：各点で同値な coherent 比較から抽出した単位は標準写像空間条件を満たす。
方針：各点の比較と標準比較の実際のホモトピーで同値性を移す。
規約：元の単位を取り出す選択は不要。使われ方：Cor 6.2.6.5 の指定単位版への接続。 -/
lemma unitMappingSpaceCondition [Quasicategory X] [Quasicategory Y]
    (hq : q.IsPointwiseEquivalence) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition q.unitHom := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitMappingSpaceCondition_iff_interval q.unitHom).mpr
  intro x y
  exact ((hq x y).isQCatEquivalence.ofFunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy (q.intervalMap_unitIntervalMap_homotopy x y).some)
  ).isSimplicialHomotopyEquivalence

/-- 概要：coherent 比較の局所同値性と抽出単位の標準条件は同値。
方針：標準比較との実際のホモトピーで同値性を双方向に移す。
規約：全パラメータの全単射を仮定しない。
使われ方：指定単位から比較を作る順方向の同値性の検証。 -/
lemma isPointwiseEquivalence_iff_unitMappingSpaceCondition [Quasicategory X] [Quasicategory Y] :
    q.IsPointwiseEquivalence ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition q.unitHom := by
  constructor
  · exact q.unitMappingSpaceCondition
  · intro h x y
    have hs := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitMappingSpaceCondition_iff_interval q.unitHom).mp h x y
    exact (hs.isQCatEquivalence.ofFunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy (q.intervalMap_unitIntervalMap_homotopy x y).some).symm
    ).isSimplicialHomotopyEquivalence

/-- 概要：単位を入力しない各点で同値な coherent 比較から随伴を構成する。
方針：抽出単位の各点の条件に証明済みの指定単位の局所判定を適用する。
規約：二つの三角恒等式は h Fun 全体で成り立つ。
使われ方：自然な写像空間対応から随伴への逆方向の具体的な実現。 -/
def adjunctionOfPointwiseEquivalence [Quasicategory X] [Quasicategory Y]
    (hq : q.IsPointwiseEquivalence) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatAdjunctionOfUnitMappingSpaceCondition q.unitHom (q.unitMappingSpaceCondition hq)

/-- 概要：構成した随伴の単位は恒等矢印の族から抽出した単位。
方針：指定単位版の回収公式を使う。
規約：h Fun の射としての等式。使われ方：元の比較との整合性。 -/
lemma adjunctionOfPointwiseEquivalence_unitHom [Quasicategory X] [Quasicategory Y]
    (hq : q.IsPointwiseEquivalence) : (q.adjunctionOfPointwiseEquivalence hq).unitHom = q.unitHom :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatAdjunctionOfUnitMappingSpaceCondition_unitHom _ _

end MappingArrowComparison
end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
