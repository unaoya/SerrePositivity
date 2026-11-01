module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FreeQuiverCoverFiberDiagram
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ColimitGraph

/-!
# 全語の値の fiber の nerve と被覆 hammock の同型

概要：元の全語の値の fiber の nerve の図式と被覆の hammock 図式を同定する。
方針：元の圏値図式の同型に nerve と余極限を適用する。
規約：全単体作用素への整合と元の各標準射を保持する。
使われ方：元の hammock の値の fiber と被覆の hammock の比較。
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

def fiberGraphDiagram : Word ⥤ SSet.{max u v} := fiberCategoryDiagram A Y β ⋙ nerveFunctor

def coverGraphDiagram : letI := quiver A; Word ⥤ SSet.{max u v} := by
  letI := quiver A
  exact graphDiagram (⊤ : MorphismProperty (Paths (Vertex A)))
    ((Paths.of (Vertex A)).obj (root A))
    ((Paths.of (Vertex A)).obj (fiberEndpoint A Y β))

def fiberGraphDiagramIso :
    letI := quiver A
    fiberGraphDiagram A Y β ≅ coverGraphDiagram A Y β := by
  letI := quiver A
  exact CategoryTheory.Functor.isoWhiskerRight (fiberCategoryDiagramIso A Y β) nerveFunctor

lemma fiberGraphDiagramIso_hom_app (w : Word) :
    letI := quiver A
    (fiberGraphDiagramIso A Y β).hom.app w = nerveMap (zigzagLiftFunctor A w Y β) := by
  let := quiver A
  rfl

lemma fiberGraphDiagramIso_inv_app (w : Word) :
    letI := quiver A
    (fiberGraphDiagramIso A Y β).inv.app w = nerveMap (zigzagFiberProjection A w Y β) := by
  let := quiver A
  rfl

def fiberGraphColimitIso :
    letI := quiver A
    colimit (fiberGraphDiagram A Y β) ≅
      colimitGraph (⊤ : MorphismProperty (Paths (Vertex A)))
        ((Paths.of (Vertex A)).obj (root A))
        ((Paths.of (Vertex A)).obj (fiberEndpoint A Y β)) := by
  letI := quiver A
  exact colim.mapIso (fiberGraphDiagramIso A Y β)

lemma fiberGraphColimitIso_fac (w : Word) :
    letI := quiver A
    colimit.ι (fiberGraphDiagram A Y β) w ≫ (fiberGraphColimitIso A Y β).hom =
      nerveMap (zigzagLiftFunctor A w Y β) ≫
        graphInclusion (⊤ : MorphismProperty (Paths (Vertex A)))
          ((Paths.of (Vertex A)).obj (root A))
          ((Paths.of (Vertex A)).obj (fiberEndpoint A Y β)) w := by
  let := quiver A
  exact colimit.ι_map (fiberGraphDiagramIso A Y β).hom w

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
