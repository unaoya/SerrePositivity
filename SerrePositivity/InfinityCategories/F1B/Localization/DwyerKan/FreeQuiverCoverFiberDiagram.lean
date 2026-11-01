module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FreeQuiverCoverFiberWordLaws
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.Diagram

/-!
# 全語の元の値の fiber と被覆の圏値図式の同型

概要：全ての元の語とその全作用に自然な圏値図式の同型を構成する。
方針：元の制限された語の作用と両関手の厳密な自然性を使う。
規約：空語・列の圧縮・恒等列の挿入を含む元の添字圏を使う。
使われ方：元の全語の nerve とその余極限の比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q) (Y : Paths Q)
  (β : (Quiver.FreeGroupoid.of Q).obj A ⟶ positiveEvaluation.obj Y)

def fiberCategoryDiagram : Word ⥤ Cat.{max u v, max u v} where
  obj w := Cat.of (ZigzagValueFiber A w Y β)
  map f := (zigzagFiberWordAction A Y β f).toCatHom
  map_id w := by apply Cat.Hom.ext; exact zigzagFiberWordAction_id A w
  map_comp f g := by apply Cat.Hom.ext; exact zigzagFiberWordAction_comp A f g

def coverCategoryDiagram : letI := quiver A; Word ⥤ Cat.{max u v, max u v} := by
  letI := quiver A
  exact categoryDiagram (⊤ : MorphismProperty (Paths (Vertex A)))
    ((Paths.of (Vertex A)).obj (root A))
    ((Paths.of (Vertex A)).obj (fiberEndpoint A Y β))

def fiberCategoryDiagramIso :
    letI := quiver A
    fiberCategoryDiagram A Y β ≅ coverCategoryDiagram A Y β := by
  letI := quiver A
  exact NatIso.ofComponents (fun w => zigzagFiberCategoryIso A w Y β) (by
    intro a b f
    apply Cat.Hom.ext
    exact zigzagLiftFunctor_wordAction A Y β f)

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
