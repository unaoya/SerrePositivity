module

public import SerrePositivity.EInfinity.Hammock.FreeQuiverCoverZigzagLiftMap

/-!
# 元の値の fiber の固定端点への持ち上げ関手

概要：元の全指定 zigzag の値を固定した全部分圏を被覆の zigzag 圏へ送る。
方針：証明済みの対象・全縦射の持ち上げを関手に束ねる。
規約：元の恒等射と合成を忠実な射影で検査する。
使われ方：元の hammock の fiber と木上の hammock の比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q) (w : Word) (Y : Paths Q)
  (β : (Quiver.FreeGroupoid.of Q).obj A ⟶ positiveEvaluation.obj Y)

def zigzagLiftFunctor :
    letI := quiver A
    ZigzagValueFiber A w Y β ⥤ Zigzag (⊤ : MorphismProperty (Paths (Vertex A))) w
      ((Paths.of (Vertex A)).obj (root A))
      ((Paths.of (Vertex A)).obj (fiberEndpoint A Y β)) := by
  letI := quiver A
  letI := pathProjection_faithful A
  exact
    { obj := zigzagLift A
      map := zigzagLiftMap A
      map_id := fun S => Zigzag.hom_ext _ _ (fun j => by
        apply (pathProjection A).map_injective
        exact (zigzagLiftMap_app_projection A (𝟙 S) j).trans
          ((pathProjection A).map_id ((zigzagLift A S).vertex j)).symm)
      map_comp := fun f g => Zigzag.hom_ext _ _ (fun j => by
        apply (pathProjection A).map_injective
        change (pathProjection A).map ((zigzagLiftMap A (f ≫ g)).app j) =
          (pathProjection A).map ((zigzagLiftMap A f).app j ≫ (zigzagLiftMap A g).app j)
        rw [CategoryTheory.Functor.map_comp, zigzagLiftMap_app_projection,
          zigzagLiftMap_app_projection, zigzagLiftMap_app_projection]
        rfl) }

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
