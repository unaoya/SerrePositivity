module
public import SerrePositivity.KST.SConstruction.RelativeCofiberModel
public import SerrePositivity.KST.SConstruction.ObjectSMonomorphisms

/-! # 閉じた全部分圏への object S 単体の持ち上げ
概要：全 Ar 成分が頂点条件を満たす gapped 図式は閉じた全部分圏に厳密に持ち上がる。
方針：実図式を全部分複体へ持ち上げ、gapped 性を周囲から反映する。
規約：object S の零頂点だけの条件では代用しない。使われ方：相対 McCarthy ホモトピー。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- object S 単体の全 Ar 成分が指定した部分圏に入るという条件。 -/
def ObjectSInClosed {X : StableModel.{u}} (P : ClosedStablePredicate X)
    {n : SimplexCategoryᵒᵖ} (v : (objectSConstruction X.carrier).obj n) : Prop :=
  ∀ a : (arNerve n.unop.len) _⦋0⦌,
    P.predicate ((gappedDiagram v).app (Opposite.op ⦋0⦌) a)

/-- 部分圏からの object S 単体の像は全 Ar 成分で条件を満たす。 -/
lemma objectSClosedInclusion_mem {X : StableModel.{u}} (P : ClosedStablePredicate X)
    (n : SimplexCategoryᵒᵖ) (v : (objectSConstruction (closedSubcategory P)).obj n) :
    ObjectSInClosed P ((objectSConstructionFunctor.map (closedStableInclusion P)).app n v) := by
  intro a
  rw [gappedDiagram_objectSFunctor_map]
  exact closedSubcategory_vertex P ((gappedDiagram v).app (Opposite.op ⦋0⦌) a)

/-- 閉じた全部分圏に入る Ar 図式を元の object S 単体として持ち上げる。 -/
def objectSClosedVertexLift {X : StableModel.{u}} (P : ClosedStablePredicate X)
    {n : SimplexCategoryᵒᵖ} (v : (objectSConstruction X.carrier).obj n) (hv : ObjectSInClosed P v) :
    (objectSConstruction (closedSubcategory P)).obj n :=
  gappedObjectVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift P.predicate (gappedDiagram v) hv) (by
    apply IsGapped.of_fullSubcomplex P.predicate
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]
    exact gappedDiagram_isGapped v)

/-- 持ち上げた object S 単体の実図式は元の実図式を厳密に回収する。 -/
lemma objectSClosedVertexLift_diagram {X : StableModel.{u}} (P : ClosedStablePredicate X)
    {n : SimplexCategoryᵒᵖ} (v : (objectSConstruction X.carrier).obj n) (hv : ObjectSInClosed P v) :
    gappedDiagram (objectSClosedVertexLift P v hv) ≫ (closedStableInclusion P).val =
      gappedDiagram v := by
  rw [objectSClosedVertexLift, gappedDiagram_gappedObjectVertex]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 持ち上げを元の包含で戻すと object S の単体を厳密に回収する。 -/
lemma objectSClosedVertexLift_inclusion {X : StableModel.{u}} (P : ClosedStablePredicate X)
    {n : SimplexCategoryᵒᵖ} (v : (objectSConstruction X.carrier).obj n) (hv : ObjectSInClosed P v) :
    (objectSConstructionFunctor.map (closedStableInclusion P)).app n
      (objectSClosedVertexLift P v hv) = v := by
  apply gappedDiagram_injective
  rw [gappedDiagram_objectSFunctor_map, objectSClosedVertexLift_diagram]

/-- 閉じた全部分圏への所属は object S の面・退化で保たれる。 -/
lemma ObjectSInClosed.map {X : StableModel.{u}} (P : ClosedStablePredicate X)
    {n m : SimplexCategoryᵒᵖ} {v : (objectSConstruction X.carrier).obj n}
    (hv : ObjectSInClosed P v) (α : n ⟶ m) :
    ObjectSInClosed P ((objectSConstruction X.carrier).map α v) := by
  intro a
  rw [gappedDiagram_objectS_map]
  exact hv ((arNerveMap α.unop.toOrderHom).app (Opposite.op ⦋0⦌) a)

end SerrePositivity.KST.SConstruction
