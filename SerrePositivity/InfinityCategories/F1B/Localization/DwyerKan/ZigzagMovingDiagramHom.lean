module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagMovingDiagramAppend

/-!
# 動く局所端点を保つ図式間の比較

概要：同じ二つの端点関手を持つ局所図式の、両端で恒等な自然な縦比較。
方針：元の MovingHom の成分と自然性を記録する。
規約：添字方向の端点の射は動く。図式間の比較だけが両端で恒等。
使われ方：局所置換の counit/unit を前後の語の図式と貼り合わせる。
-/

@[expose] public section
universe u v u' v'
namespace SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram
open CategoryTheory

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {w : Word} {A B : D ⥤ C}

structure Hom (F G : MovingDiagram D C W w A B) where
  app : ∀ d, MovingHom (F.obj d) (G.obj d)
  naturality : ∀ {d d'} (f : d ⟶ d'), (F.map f).comp (app d') = (app d).comp (G.map f)
  first : ∀ d, HEq ((app d).app 0) (𝟙 (A.obj d))
  last : ∀ d, HEq ((app d).app (Fin.last w.length)) (𝟙 (B.obj d))

namespace Hom

def id (F : MovingDiagram D C W w A B) : Hom F F where
  app d := MovingHom.id (F.obj d)
  naturality _ := by
    apply MovingHom.ext
    intro j
    dsimp only [MovingHom.comp, MovingHom.id]
    simp
  first d := MovingHom.id_first (F.obj d)
  last d := MovingHom.id_last (F.obj d)

end Hom
end SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram
