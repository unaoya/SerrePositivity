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
  (β : (Quiver.FreeGroupoid.of Q).obj A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.obj Y)

def hammockValueFiber : SSet.{max u v} := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialValueFiber.space (hammockValue A Y) β

def valueFiberColimitIso : colimit (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fiberGraphDiagram A Y β) ≅ hammockValueFiber A Y β :=
  colim.mapIso (fiberValueDiagramIso A Y β) ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialLabelledColimit.colimitFiberIso (graphValueLabels A Y) β

def hammockValueFiberCoverIso :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    hammockValueFiber A Y β ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph (⊤ : MorphismProperty (Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)))
        ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.root A))
        ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fiberEndpoint A Y β)) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  exact (valueFiberColimitIso A Y β).symm ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fiberGraphColimitIso A Y β

lemma valueFiberColimitIso_fac_inclusion (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fiberGraphDiagram A Y β) w ≫ (valueFiberColimitIso A Y β).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialValueFiber.inclusion (hammockValue A Y) β =
        nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagValueProperty A w Y β).ι ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion (⊤ : MorphismProperty (Paths Q)) ((Paths.of Q).obj A) Y w := by
  let L := graphValueLabels A Y
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialLabelledColimit.colimitFiberIso L β
  let inc := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialValueFiber.inclusion (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialLabelledDiagram.colimitValue L) β
  change colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fiberGraphDiagram A Y β) w ≫
    (colim.map (fiberValueDiagramIso A Y β).hom ≫ e.hom) ≫ inc =
      nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagValueProperty A w Y β).ι ≫
        colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (⊤ : MorphismProperty (Paths Q)) ((Paths.of Q).obj A) Y) w
  have hc := congrArg (fun p => p ≫ e.hom ≫ inc)
    (colimit.ι_map (fiberValueDiagramIso A Y β).hom w)
  calc
    _ = ((fiberValueDiagramIso A Y β).hom.app w ≫
        colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialLabelledDiagram.fiberDiagram L β) w) ≫ e.hom ≫ inc := by
      simpa only [Category.assoc] using hc
    _ = (fiberValueDiagramIso A Y β).hom.app w ≫
        (colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialLabelledDiagram.fiberDiagram L β) w ≫ e.hom ≫ inc) := by
      simp only [Category.assoc]
    _ = (fiberValueDiagramIso A Y β).hom.app w ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialValueFiber.inclusion (L.value w) β ≫
          colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (⊤ : MorphismProperty (Paths Q)) ((Paths.of Q).obj A) Y) w) :=
      congrArg (fun p => (fiberValueDiagramIso A Y β).hom.app w ≫ p)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialLabelledColimit.colimitFiberIso_fac_inclusion L β w)
    _ = _ := ((Category.assoc _ _ _).symm).trans
      (congrArg (fun p => p ≫
        colimit.ι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (⊤ : MorphismProperty (Paths Q)) ((Paths.of Q).obj A) Y) w)
          (fiberValueDiagramIso_hom_inclusion A Y β w))

def existingHammockValueFiberCoverIso {Q' : Type u} [Quiver.{u} Q'] (A' : Q') (Y' : Paths Q')
    (β' : (Quiver.FreeGroupoid.of Q').obj A' ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.obj Y') :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A'
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialValueFiber.space (Zigzag.Value.colimitValue _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation_inverts_top ((Paths.of Q').obj A') Y') β' ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph (⊤ : MorphismProperty (Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A')))
        ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A')).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.root A'))
        ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A')).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fiberEndpoint A' Y' β')) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A'
  exact (eqToIso (congrArg (fun f => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SimplicialValueFiber.space f β')
    (hammockValue_eq_colimitValue A' Y'))).symm ≪≫ hammockValueFiberCoverIso A' Y' β'

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
