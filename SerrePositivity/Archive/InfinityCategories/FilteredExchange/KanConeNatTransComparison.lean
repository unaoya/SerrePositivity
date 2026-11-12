module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.KanConeDiagramComparisonIsos
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.StrictDiagramTriangleConstant
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceTriangleConstantFaces
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.HomotopyVerticalRestriction
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.StrictCoherentNatTransComponent
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorEqIsoAlgebra

/-!
概要：通常の自然変換の指定円柱に沿う Kan 錐比較の図式成分と二次比較。
方針：元の図式制限を頂点と二単体で評価する。
規約：元の自然変換と指定同型を保持。使われ方：区間錐の切断との整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {I : Type u} [SmallCategory I] {F G : I ⥤ KanObject.{u}}
  {c : JoinCone (kanDiagramCoherentNerve F)} {d : JoinCone (kanDiagramCoherentNerve G)}
  (T : SSet.Homotopy c.val d.val) (η : F ⟶ G)
  (hD : (joinInr _ _ ▷ (Δ[1] : SSet.{u + 1})) ≫ T.h =
    (β_ _ (Δ[1] : SSet.{u + 1})).hom ≫ strictCoherentNatTransMap η)

include hD

/-- 概要：図式成分の読み戻しは元の自然変換の成分。
方針：元の頂点辺を評価。規約：射の厳密な式。使われ方：自然性の端点の同定。 -/
lemma kanConeDiagramComponent_eq_app (i : I) : kanConeDiagramComponent T i = η.app i := by
  have h := homotopyVertexEdge_prism T (joinInr _ _) (strictCoherentNatTransMap η) hD
    (ULift.up (ComposableArrows.mk₀ i))
  have he := (kanConeDiagramComponent_edge T i).trans
    (h.trans (strictCoherentNatTransMap_component η i))
  exact eq_of_heq ((heq_of_eq (coherentEdgeHom_edge (kanConeDiagramComponent T i))).symm.trans
    (coherentEdgeHom_of_edge_eq he))

/-- 概要：図式上側の指定同型は元の自然性の等式から来る。
方針：strict 円柱の元の二単体は豊穣辺が定値。規約：指定値。使われ方：二次の簡約。 -/
lemma kanConeDiagramUpperIso_natTrans_isFunctorEqIso {i j : I} (f : i ⟶ j) :
    IsFunctorEqIso (kanConeDiagramUpperIso T f) := by
  apply isFunctorEqIso_spaceInfinityTriangleIso_of_faces
  exact isConstantCoherentTriangle_natTrans_upper η (joinInr _ _) T.h hD _

/-- 概要：図式下側の指定同型は元の自然性の等式から来る。
方針：strict 円柱の元の二単体は豊穣辺が定値。規約：指定値。使われ方：二次の簡約。 -/
lemma kanConeDiagramLowerIso_natTrans_isFunctorEqIso {i j : I} (f : i ⟶ j) :
    IsFunctorEqIso (kanConeDiagramLowerIso T f) := by
  apply isFunctorEqIso_spaceInfinityTriangleIso_of_faces
  exact isConstantCoherentTriangle_natTrans_lower η (joinInr _ _) T.h hD _

/-- 概要：図式の指定比較そのものは元の自然性等式から来る同型。
方針：元の上下同型の反転と合成。規約：指定値。使われ方：区間錐の整合式の簡約。 -/
lemma kanConeDiagramComparisonIso_natTrans_isFunctorEqIso {i j : I} (f : i ⟶ j) :
    IsFunctorEqIso (kanConeDiagramComparisonIso T f) :=
  (kanConeDiagramLowerIso_natTrans_isFunctorEqIso T η hD f).symm.trans
    (kanConeDiagramUpperIso_natTrans_isFunctorEqIso T η hD f)

end SerrePositivity.InfinityCategories.F2
