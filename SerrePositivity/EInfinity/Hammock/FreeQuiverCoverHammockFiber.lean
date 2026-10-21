module

public import SerrePositivity.EInfinity.Hammock.FreeQuiverCoverValueFiberDiagram

/-!
# 元の hammock の値の fiber と被覆の元の hammock の同型

概要：元の hammock 上で値 β を持つ単体を被覆の固定端点 hammock に同定する。
方針：元の graph の fiber の図式の同型と fiber の余極限性を合成する。
規約：元の評価と各語の元の標準射を回収する。
使われ方：全指定自由圏の元の hammock の成分可縮性。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory CategoryTheory.Limits

variable {Q : Type u} [Quiver.{v} Q] (A : Q) (Y : Paths Q)
  (β : (Quiver.FreeGroupoid.of Q).obj A ⟶ positiveEvaluation.obj Y)

def hammockValueFiber : SSet.{max u v} := SimplicialValueFiber.space (hammockValue A Y) β

def valueFiberColimitIso : colimit (fiberGraphDiagram A Y β) ≅ hammockValueFiber A Y β :=
  colim.mapIso (fiberValueDiagramIso A Y β) ≪≫
    SimplicialLabelledColimit.colimitFiberIso (graphValueLabels A Y) β

def hammockValueFiberCoverIso :
    letI := quiver A
    hammockValueFiber A Y β ≅
      colimitGraph (⊤ : MorphismProperty (Paths (Vertex A)))
        ((Paths.of (Vertex A)).obj (root A))
        ((Paths.of (Vertex A)).obj (fiberEndpoint A Y β)) := by
  letI := quiver A
  exact (valueFiberColimitIso A Y β).symm ≪≫ fiberGraphColimitIso A Y β

lemma valueFiberColimitIso_fac_inclusion (w : Word) :
    colimit.ι (fiberGraphDiagram A Y β) w ≫ (valueFiberColimitIso A Y β).hom ≫
      SimplicialValueFiber.inclusion (hammockValue A Y) β =
        nerveMap (zigzagValueProperty A w Y β).ι ≫
          graphInclusion (⊤ : MorphismProperty (Paths Q)) ((Paths.of Q).obj A) Y w := by
  let L := graphValueLabels A Y
  let e := SimplicialLabelledColimit.colimitFiberIso L β
  let inc := SimplicialValueFiber.inclusion (SimplicialLabelledColimit.colimitValue L) β
  change colimit.ι (fiberGraphDiagram A Y β) w ≫
    (colim.map (fiberValueDiagramIso A Y β).hom ≫ e.hom) ≫ inc =
      nerveMap (zigzagValueProperty A w Y β).ι ≫
        colimit.ι (graphDiagram (⊤ : MorphismProperty (Paths Q)) ((Paths.of Q).obj A) Y) w
  have hc := congrArg (fun p => p ≫ e.hom ≫ inc)
    (colimit.ι_map (fiberValueDiagramIso A Y β).hom w)
  calc
    _ = ((fiberValueDiagramIso A Y β).hom.app w ≫
        colimit.ι (SimplicialLabelledColimit.fiberDiagram L β) w) ≫ e.hom ≫ inc := by
      simpa only [Category.assoc] using hc
    _ = (fiberValueDiagramIso A Y β).hom.app w ≫
        (colimit.ι (SimplicialLabelledColimit.fiberDiagram L β) w ≫ e.hom ≫ inc) := by
      simp only [Category.assoc]
    _ = (fiberValueDiagramIso A Y β).hom.app w ≫
        (SimplicialValueFiber.inclusion (L.value w) β ≫
          colimit.ι (graphDiagram (⊤ : MorphismProperty (Paths Q)) ((Paths.of Q).obj A) Y) w) :=
      congrArg (fun p => (fiberValueDiagramIso A Y β).hom.app w ≫ p)
        (SimplicialLabelledColimit.colimitFiberIso_fac_inclusion L β w)
    _ = _ := ((Category.assoc _ _ _).symm).trans
      (congrArg (fun p => p ≫
        colimit.ι (graphDiagram (⊤ : MorphismProperty (Paths Q)) ((Paths.of Q).obj A) Y) w)
          (fiberValueDiagramIso_hom_inclusion A Y β w))

def existingHammockValueFiberCoverIso {Q' : Type u} [Quiver.{u} Q'] (A' : Q') (Y' : Paths Q')
    (β' : (Quiver.FreeGroupoid.of Q').obj A' ⟶ positiveEvaluation.obj Y') :
    letI := quiver A'
    SimplicialValueFiber.space (Zigzag.Value.colimitValue positiveEvaluation
      positiveEvaluation_inverts_top ((Paths.of Q').obj A') Y') β' ≅
      colimitGraph (⊤ : MorphismProperty (Paths (Vertex A')))
        ((Paths.of (Vertex A')).obj (root A'))
        ((Paths.of (Vertex A')).obj (fiberEndpoint A' Y' β')) := by
  letI := quiver A'
  exact (eqToIso (congrArg (fun f => SimplicialValueFiber.space f β')
    (hammockValue_eq_colimitValue A' Y'))).symm ≪≫ hammockValueFiberCoverIso A' Y' β'

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
