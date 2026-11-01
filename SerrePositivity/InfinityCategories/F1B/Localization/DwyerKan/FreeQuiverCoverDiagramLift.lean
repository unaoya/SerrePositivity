module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FreeQuiverCoverDiagramLabels

/-!
# ラベルを持つ元の図式の関手としての持ち上げ

概要：ラベルが整合する元の図式を被覆の自由圏へ持ち上げる。
方針：指定両端の射列の持ち上げと射影の忠実性を使う。
規約：元の全図式を射影で厳密に回収する。
使われ方：hammock の全縦射と各行の持ち上げ。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q) {D : Type u'} [Category.{v'} D]
  {F : D ⥤ Paths Q} (L : DiagramLabels A F)

def diagramLift : letI := quiver A; D ⥤ Paths (Vertex A) := by
  letI := quiver A
  letI := pathProjection_faithful A
  exact
    { obj := fun d => (Paths.of (Vertex A)).obj (DiagramLabels.vertex A L d)
      map := fun f => liftPathTo A (DiagramLabels.vertex A L _)
        (DiagramLabels.vertex A L _) (F.map f) (L.naturality f)
      map_id := fun d => by
        apply (pathProjection A).map_injective
        exact (liftPathTo_projection A _ _ _ _).trans (F.map_id d)
      map_comp := fun f g => by
        apply (pathProjection A).map_injective
        change (projection A).mapPath (liftPathTo A _ _ _ _) =
          (projection A).mapPath ((liftPathTo A _ _ _ _).comp (liftPathTo A _ _ _ _))
        rw [Prefunctor.mapPath_comp, liftPathTo_projection,
          liftPathTo_projection, liftPathTo_projection]
        exact F.map_comp f g }

lemma diagramLift_projection :
    letI := quiver A
    diagramLift A L ⋙ pathProjection A = F := by
  let := quiver A
  apply CategoryTheory.Functor.hext (F := diagramLift A L ⋙ pathProjection A) (G := F)
  · intro d
    rfl
  · intro d e f
    exact heq_of_eq (liftPathTo_projection A (DiagramLabels.vertex A L d)
      (DiagramLabels.vertex A L e) (F.map f) (L.naturality f))

lemma diagramLift_map_projection {d e : D} (f : d ⟶ e) :
    letI := quiver A
    (pathProjection A).map ((diagramLift A L).map f) = F.map f := by
  let := quiver A
  exact liftPathTo_projection A (DiagramLabels.vertex A L d)
    (DiagramLabels.vertex A L e) (F.map f) (L.naturality f)

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
