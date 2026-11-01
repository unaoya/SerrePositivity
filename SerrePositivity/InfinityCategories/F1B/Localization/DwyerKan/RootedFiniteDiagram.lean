module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.RootedFiniteProjection
public import Mathlib.CategoryTheory.Category.Preorder

/-!
# 元の有限部分集合による固定語の strict 圏値・nerve 図式

概要：有限集合の包含を添字として元の各固定語の圏を並べる。
方針：証明済みの元の包含の恒等・合成則をそのまま使う。
規約：全体への元の射影を余錐の各脚にする。
使われ方：全被覆の固定語の graph の filtered 余極限表示。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.RootedFinite
open CategoryTheory Limits
attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] (T : WideSubquiver (Quiver.Symmetrify Q))
  [Quiver.Arborescence T] (X Y : Q)

def categoryDiagram (a : Word) : Finset Q ⥤ Cat.{max u v, max u v} where
  obj S := termCategory T X Y a S
  map h := (mapFunctor T X Y a (leOfHom h)).toCatHom
  map_id S := by
    apply Cat.Hom.ext
    exact mapFunctor_id T X Y a S
  map_comp h k := by
    apply Cat.Hom.ext
    exact mapFunctor_comp T X Y a (leOfHom h) (leOfHom k)

def graphDiagram (a : Word) : Finset Q ⥤ SSet.{max u v} :=
  categoryDiagram T X Y a ⋙ nerveFunctor

def categoryCocone (a : Word) : Cocone (categoryDiagram T X Y a) where
  pt := Cat.of (Zigzag (⊤ : MorphismProperty (Paths Q)) a ((Paths.of Q).obj X) ((Paths.of Q).obj Y))
  ι :=
    { app S := (projectionFunctor T X Y a S).toCatHom
      naturality S R h := by
        apply Cat.Hom.ext
        change mapFunctor T X Y a (leOfHom h) ⋙ projectionFunctor T X Y a R =
          projectionFunctor T X Y a S ⋙ 𝟭 _
        rw [Functor.comp_id]
        exact mapFunctor_projection T X Y a (leOfHom h) }

def graphCocone (a : Word) : Cocone (graphDiagram T X Y a) :=
  nerveFunctor.mapCocone (categoryCocone T X Y a)

end SerrePositivity.EInfinity.Hammock.RootedFinite
