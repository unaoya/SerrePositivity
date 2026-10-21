module

public import SerrePositivity.EInfinity.Hammock.FreeQuiverCoverZigzagLift

/-!
# 元の全縦射と全可換正方形の持ち上げ

概要：値を固定した元の zigzag 間の全縦射を固定端点のまま持ち上げる。
方針：接頭ラベルの自然性で各成分を持ち上げ、忠実性で正方形を照合する。
規約：元の全成分・端点の恒等射・正方形を射影で回収する。
使われ方：固定端点の zigzag の圏の持ち上げ関手。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q) {w : Word} {Y : Paths Q}
  {β : (Quiver.FreeGroupoid.of Q).obj A ⟶ positiveEvaluation.obj Y}

def zigzagLiftMap {S T : ZigzagValueFiber A w Y β} (f : S ⟶ T) :
    letI := quiver A
    Zigzag.Hom (zigzagLift A S) (zigzagLift A T) := by
  letI := quiver A
  letI := pathProjection_faithful A
  let app : ∀ j, (zigzagLift A S).vertex j ⟶ (zigzagLift A T).vertex j := fun j =>
    liftPathTo A (zigzagVertex A S.obj j) (zigzagVertex A T.obj j) (f.hom.app j)
      (zigzagPrefix_naturality A f.hom j)
  have hp : ∀ j, (pathProjection A).map (app j) = f.hom.app j := fun j =>
    liftPathTo_projection A (zigzagVertex A S.obj j) (zigzagVertex A T.obj j) (f.hom.app j)
      (zigzagPrefix_naturality A f.hom j)
  exact
    { app := app
      app_mem := fun _ => trivial
      first := by
        apply (pathProjection A).map_injective
        calc
          _ = f.hom.app 0 := hp 0
          _ = eqToHom (S.obj.first.trans T.obj.first.symm) := f.hom.first
          _ = _ := (eqToHom_map (pathProjection A)
            ((zigzagLift A S).first.trans (zigzagLift A T).first.symm)).symm
      last := by
        apply (pathProjection A).map_injective
        calc
          _ = f.hom.app (Fin.last w.length) := hp _
          _ = eqToHom (S.obj.last.trans T.obj.last.symm) := f.hom.last
          _ = _ := (eqToHom_map (pathProjection A)
            ((zigzagLift A S).last.trans (zigzagLift A T).last.symm)).symm
      comm := fun i => by
        apply (pathProjection A).map_injective
        rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
          zigzagLift_arrow_projection, zigzagLift_arrow_projection, hp, hp]
        exact f.hom.comm i }

lemma zigzagLiftMap_app_projection {S T : ZigzagValueFiber A w Y β} (f : S ⟶ T)
    (j : Fin (w.length + 1)) :
    letI := quiver A
    (pathProjection A).map ((zigzagLiftMap A f).app j) = f.hom.app j := by
  let := quiver A
  exact liftPathTo_projection A (zigzagVertex A S.obj j) (zigzagVertex A T.obj j) (f.hom.app j)
    (zigzagPrefix_naturality A f.hom j)

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
