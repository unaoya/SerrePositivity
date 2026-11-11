module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverDiagramLabels

/-!
# ラベルを持つ元の図式の関手としての持ち上げ

概要：ラベルが整合する元の図式を被覆の自由圏へ持ち上げる。
方針：指定両端の射列の持ち上げと射影の忠実性を使う。
規約：元の全図式を射影で厳密に回収する。
使われ方：hammock の全縦射と各行の持ち上げ。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q) {D : Type u'} [Category.{v'} D]
  {F : D ⥤ Paths Q} (L : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiagramLabels A F)

def diagramLift : letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A; D ⥤ Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathProjection_faithful A
  exact
    { obj := fun d => (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiagramLabels.vertex A L d)
      map := fun f => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.liftPathTo A (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiagramLabels.vertex A L _)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiagramLabels.vertex A L _) (F.map f) (L.naturality f)
      map_id := fun d => by
        apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathProjection A).map_injective
        exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.liftPathTo_projection A _ _ _ _).trans (F.map_id d)
      map_comp := fun f g => by
        apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathProjection A).map_injective
        change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.projection A).mapPath (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.liftPathTo A _ _ _ _) =
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.projection A).mapPath ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.liftPathTo A _ _ _ _).comp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.liftPathTo A _ _ _ _))
        rw [Prefunctor.mapPath_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.liftPathTo_projection,
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.liftPathTo_projection, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.liftPathTo_projection]
        exact F.map_comp f g }

lemma diagramLift_projection :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    diagramLift A L ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathProjection A = F := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  apply CategoryTheory.Functor.hext (F := diagramLift A L ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathProjection A) (G := F)
  · intro d
    rfl
  · intro d e f
    exact heq_of_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.liftPathTo_projection A (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiagramLabels.vertex A L d)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiagramLabels.vertex A L e) (F.map f) (L.naturality f))

lemma diagramLift_map_projection {d e : D} (f : d ⟶ e) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathProjection A).map ((diagramLift A L).map f) = F.map f := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.liftPathTo_projection A (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiagramLabels.vertex A L d)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiagramLabels.vertex A L e) (F.map f) (L.naturality f)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
