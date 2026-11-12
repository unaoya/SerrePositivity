module
public import SerrePositivity.KST.SConstruction.FamilyChainRectangleComparison

/-! # 元の三角形・全交換列・共有末尾による全辺路の比較
概要：三角形に貼った長方形の全交換列と同じ末尾から、二つの全辺路を実比較する。
方針：元の三角形の合成式と全交換セルの長方形式を合成し、実三角形へ戻す。
規約：両側の元の全区間と末尾を保持し、異なる列の比較の存在を入力にしない。
使われ方：次段の全射影 trace と前段の全構造射 trace の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {U E : SSet.{u}} {f g : U ⊗ (Δ[1] : SSet.{u}) ⟶ E} {a b : U ⟶ E}
  (first : SSet.Homotopy a (SSet.ι₀ ≫ f))
  (direct : SSet.Homotopy a (SSet.ι₁ ≫ f))
  (triangle : SSet.Edge.CompStruct
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy first))
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (familyCylinder f)))
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy direct)))
  (c : FamilyHomotopyChain f g) (tail : FamilyHomotopyChain (SSet.ι₁ ≫ g) b)

/-- 元の合成面・一側の全交換境界・共通末尾の全辺路。 -/
def familyTriangleStripDirect : FamilyHomotopyChain a b :=
  .cons direct (familyHomotopyChainAppend (familyHomotopyChainPrecomp SSet.ι₁ c) tail)

/-- 元の第一面・他側の全交換境界・出口・共通末尾の全辺路。 -/
def familyTriangleStripProjected : FamilyHomotopyChain a b :=
  .cons first (familyHomotopyChainAppend (familyChainRectangleRight c) tail)

/-- 一側の全区間と末尾を厳密に回収する。 -/
lemma familyTriangleStripDirect_trace :
    familyHomotopyChainTrace (familyTriangleStripDirect direct c tail) =
      direct.h :: ((familyHomotopyChainTrace c).map
        ((SSet.ι₁ (X := U) ▷ (Δ[1] : SSet.{u})) ≫ ·) ++ familyHomotopyChainTrace tail) := by
  change direct.h :: familyHomotopyChainTrace (familyHomotopyChainAppend _ _) = _
  rw [familyHomotopyChainAppend_trace, familyHomotopyChainPrecomp_trace]

/-- 他側でも全区間・出口・共通末尾の順序と個数を保持する。 -/
lemma familyTriangleStripProjected_trace :
    familyHomotopyChainTrace (familyTriangleStripProjected first c tail) =
      first.h :: ((familyHomotopyChainTrace c).map
        ((SSet.ι₀ (X := U) ▷ (Δ[1] : SSet.{u})) ≫ ·) ++
          g :: familyHomotopyChainTrace tail) := by
  change first.h :: familyHomotopyChainTrace (familyHomotopyChainAppend _ _) = _
  rw [familyHomotopyChainAppend_trace, familyChainRectangleRight_trace, List.append_assoc]
  rfl

include triangle

/-- 元の実三角形と全交換正方形により、二つの全辺路が同じ合成を表す。 -/
lemma familyTriangleStrip_class :
    familyChainCompositeClass (familyTriangleStripDirect direct c tail) =
      familyChainCompositeClass (familyTriangleStripProjected first c tail) := by
  change _ ≫ familyChainCompositeClass (familyHomotopyChainAppend _ _) =
    _ ≫ familyChainCompositeClass (familyHomotopyChainAppend _ _)
  rw [familyChainCompositeClass_append, familyChainCompositeClass_append]
  have ht : SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy first) ≫
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (familyCylinder f)) =
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy direct) :=
    SSet.HomotopyCategory.homMk_comp_homMk triangle
  rw [← ht]
  rw [Category.assoc, ← Category.assoc
    (SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (familyCylinder f)))]
  exact congrArg (fun k => SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy first) ≫ k ≫ familyChainCompositeClass tail)
      (familyChainRectangleLeft_class_eq c)

/-- 全区間と全合成三角形を保持した両辺路の実合成円柱の合成式。 -/
lemma familyTriangleStrip_composite_class_eq [KanComplex E] :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (familyChainCompositeData (familyTriangleStripDirect direct c tail)).homotopy) =
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (familyChainCompositeData (familyTriangleStripProjected first c tail)).homotopy) :=
  (familyChainCompositionWitness_class
    (familyChainCompositeData (familyTriangleStripDirect direct c tail)).witness).trans
      ((familyTriangleStrip_class first direct triangle c tail).trans
        (familyChainCompositionWitness_class
          (familyChainCompositeData (familyTriangleStripProjected first c tail)).witness).symm)

/-- 元の全セルから内部構成する、両全辺路の合成円柱の端点固定実比較。 -/
def familyTriangleStripComparison [KanComplex E] : SSet.Homotopy
    (familyChainCompositeData (familyTriangleStripDirect direct c tail)).homotopy.h
    (familyChainCompositeData (familyTriangleStripProjected first c tail)).homotopy.h :=
  familyCylinderClassComparison _ _
    (familyTriangleStrip_composite_class_eq first direct triangle c tail)

/-- 始点族は全比較時刻で固定する。 -/
lemma familyTriangleStripComparison_source [KanComplex E] :
    (SSet.ι₀ (X := U) ▷ (Δ[1] : SSet.{u})) ≫
      (familyTriangleStripComparison first direct triangle c tail).h =
        fst U (Δ[1] : SSet.{u}) ≫ a :=
  familyCylinderClassComparison_source _ _ _

/-- 終点族も全比較時刻で固定する。 -/
lemma familyTriangleStripComparison_target [KanComplex E] :
    (SSet.ι₁ (X := U) ▷ (Δ[1] : SSet.{u})) ≫
      (familyTriangleStripComparison first direct triangle c tail).h =
        fst U (Δ[1] : SSet.{u}) ≫ b :=
  familyCylinderClassComparison_target _ _ _

end SerrePositivity.KST.SConstruction
