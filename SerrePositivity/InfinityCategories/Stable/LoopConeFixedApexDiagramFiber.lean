module
public import SerrePositivity.InfinityCategories.Stable.FixedApexConeFiber
public import SerrePositivity.InfinityCategories.Stable.LoopConeFixedApexComparison
public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitCommaFiberIntervalIso

/-!
概要：固定頂点の錐と、元の図式固定の二段 fiber を同じ全空間の上で厳密に同定する。
方針：同じ円柱の厳密な式を照合し、証明済みの実区間族の同値性を戻す。
規約：安定性や有限余極限を先取りしない。使われ方：一般安定性判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 固定頂点からの同じ実 cospan の全錐を、元の図式固定 fiber と厳密に同型にする。 -/
def loopConeFixedApexDiagramFiberIso {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : LoopSquare y) (x : X _⦋0⦌) :
    HomotopyLimits.fixedApexConeFamily (pullbackCospan t.square) x ≅
      vertexFiber (loopConeSourceFiberProjection X x) t.diagramVertex :=
  fixedApexPointedConeDiagramFiberIso (pullbackCospan t.square) x ≪≫
    (eqToIso (congrArg (vertexFiber (pointedConeProjection (horn 2 2 : SSet.{u}) X x))
      (loopDiagramConeFamily_base_vertex t))).symm ≪≫
      (loopConeSourceDiagramFiberIso X x t.diagramVertex).symm

/-- 図式固定 fiber 表示の逆射は、元の全錐への二重包含を回収する。 -/
lemma loopConeSourceDiagramFiberIso_inv_diagram {X : SSet.{u}} [Quasicategory X]
    (x : X _⦋0⦌) (d : (loopDiagrams X) _⦋0⦌) :
    (loopConeSourceDiagramFiberIso X x d).inv ≫
        vertexFiberι (loopConeSourceFiberProjection X x) d ≫
          vertexFiberι (loopConeObjectSource X) x ≫ loopConeObjectDiagram X =
      vertexFiberι (pointedConeProjection (horn 2 2 : SSet.{u}) X x)
        ((loopDiagramConeFamily X ≫ limitConeProjection (horn 2 2 : SSet.{u}) X).app
          (Opposite.op ⦋0⦌) d) ≫ vertexFiberι (coneApexEvaluation (horn 2 2 : SSet.{u}) X) x := by
  let e := loopConeSourceDiagramFiberIso X x d
  have hdiag : loopConeSourceFiberDiagram X x ≫
      vertexFiberι (coneApexEvaluation (horn 2 2 : SSet.{u}) X) x =
      vertexFiberι (loopConeObjectSource X) x ≫ loopConeObjectDiagram X :=
    vertexFiberMap_ι _ _ _ _ _
  have hh := congrArg (fun f ↦ e.inv ≫ f ≫
    vertexFiberι (coneApexEvaluation (horn 2 2 : SSet.{u}) X) x)
      (loopConeSourceDiagramFiberIso_hom_ι X x d)
  simpa only [e, Category.assoc, hdiag, Iso.inv_hom_id_assoc] using hh.symm

/-- 固定頂点の錐の厳密同型は、同じ元の全錐の評価を保持する。 -/
lemma loopConeFixedApexDiagramFiberIso_diagram {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : LoopSquare y) (x : X _⦋0⦌) :
    (loopConeFixedApexDiagramFiberIso t x).hom ≫
        vertexFiberι (loopConeSourceFiberProjection X x) t.diagramVertex ≫
          vertexFiberι (loopConeObjectSource X) x ≫ loopConeObjectDiagram X =
      HomotopyLimits.fixedApexConeFamilyEvaluation (pullbackCospan t.square) x := by
  dsimp only [loopConeFixedApexDiagramFiberIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc]
  rw [loopConeSourceDiagramFiberIso_inv_diagram]
  have hi := SerrePositivity.InfinityCategories.F1B.vertexFiberι_eqTransport
    (pointedConeProjection (horn 2 2 : SSet.{u}) X x)
    (loopDiagramConeFamily_base_vertex t).symm
  have hi' : (eqToIso (congrArg (vertexFiber (pointedConeProjection (horn 2 2 : SSet.{u}) X x))
      (loopDiagramConeFamily_base_vertex t))).inv ≫
      vertexFiberι (pointedConeProjection (horn 2 2 : SSet.{u}) X x)
        ((loopDiagramConeFamily X ≫ limitConeProjection (horn 2 2 : SSet.{u}) X).app
          (Opposite.op ⦋0⦌) t.diagramVertex) =
      vertexFiberι (pointedConeProjection (horn 2 2 : SSet.{u}) X x)
        (functorVertex (pullbackCospan t.square)) := hi
  rw [reassoc_of% hi']
  exact fixedApexPointedConeDiagramFiberIso_hom_ι _ _

/-- 厳密同型を元の全空間へ含めると、同じ実 lift そのものになる。 -/
lemma loopConeFixedApexDiagramFiberIso_lift {X : SSet.{u}} [Quasicategory X]
    {y : X _⦋0⦌} (t : LoopSquare y) (x : X _⦋0⦌) :
    (loopConeFixedApexDiagramFiberIso t x).hom ≫
        vertexFiberι (loopConeSourceFiberProjection X x) t.diagramVertex ≫
          vertexFiberι (loopConeObjectSource X) x = loopConeFixedApexLift t x := by
  apply pullback.hom_ext
  · exact (loopConeFixedApexDiagramFiberIso_diagram t x).trans
      (loopConeFixedApexLift_diagram t x).symm
  · change (loopConeFixedApexDiagramFiberIso t x).hom ≫
      vertexFiberι (loopConeSourceFiberProjection X x) t.diagramVertex ≫
        loopConeSourceFiberProjection X x = _
    rw [vertexFiberι_comp, SSet.comp_const, loopConeFixedApexLift_loop]
end SerrePositivity.InfinityCategories
