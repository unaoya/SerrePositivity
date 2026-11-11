module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeVertexFiberInitial
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeCoconeAbsolute
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryMappingSpace

/-!
概要：全余錐の相対充填条件を図式固定の余錐の族の相対始対象性へ移す。
方針：余錐制限の頂点 fiber への比較を用い、相対充填と写像空間の同値を得る。
規約：標的の射 U に fibration 性は要求しない。
使われ方：操作的な相対余錐条件と標準的な U 余極限の比較。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：標的の射は図式固定の余錐の族の間の後合成を誘導する。
方針：余錐制限の自然性が与える頂点 fiber の比較を取る。
規約：像の図式は p≫U。
使われ方：固定した図式の余錐圏における相対普遍性の記述。 -/
def kanCoconeFamilyPostcomp {K D E : SSet.{u}} (p : K ⟶ D) (U : D ⟶ E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamily p ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamily (p ≫ U) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeVertexFiberMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K E)
    ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}))).map U) ((ihom K).map U)
    ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K (Δ[0] : SSet.{u}))).naturality U).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)

/-- 概要：余錐の族の後合成は指定余錐の頂点をその像の頂点へ送る。
方針：fiber の包含により内部 Hom の後合成の零次成分を計算する。
規約：余錐の図式と全余錐の射の両方を保つ。
使われ方：相対始対象性の指定頂点の同定。 -/
lemma kanCoconeFamilyPostcomp_vertex {K D E : SSet.{u}} (p : K ⟶ D) (U : D ⟶ E)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    (kanCoconeFamilyPostcomp p U).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamilyVertexEquiv p c) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamilyVertexEquiv (p ≫ U) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone U c) := by
  apply Subtype.ext
  rfl

/-- 概要：全余錐の相対充填は固定図式の余錐の族での相対始点境界充填を与える。
方針：引き戻しへの比較の相対充填を図式の頂点 fiber に制限する。
規約：U と三つの単体集合は任意。
使われ方：相対余錐条件から図式固定の相対普遍性を回収する。 -/
lemma kanCoconeFamilyPostcomp_initialBoundary {K D E : SSet.{u}}
    (p : K ⟶ D) (U : D ⟶ E) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeCoconeLifting U c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting (kanCoconeFamilyPostcomp p U) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamilyVertexEquiv p c) := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeVertexFiberMap_initialBoundary
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K E)
    ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}))).map U) ((ihom K).map U)
    ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K (Δ[0] : SSet.{u}))).naturality U).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamilyVertexEquiv p c) hc

/-- 概要：相対的に普遍な余錐から出る固定図式の写像空間の後合成は同値。
方針：余錐の族での相対始点境界充填から右 pinched 模型の比較定理を使う。
規約：D と E は quasicategory、U の充填性は不要。
使われ方：U 余極限の写像空間による特徴づけへの接続。 -/
lemma kanCoconeFamilyPostcomp_pinchedHom_equivalence {K D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (p : K ⟶ D) (U : D ⟶ E)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeCoconeLifting U c) (y : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamily p) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (kanCoconeFamilyPostcomp p U) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamilyVertexEquiv p c) y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pinchedHomMap_equivalence_of_initialBoundary (kanCoconeFamilyPostcomp p U) _ _
    (kanCoconeFamilyPostcomp_initialBoundary p U c hc)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
