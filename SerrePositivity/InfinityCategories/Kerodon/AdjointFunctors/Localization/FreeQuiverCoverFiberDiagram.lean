module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverFiberWordLaws
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram

/-!
# 全語の元の値の fiber と被覆の圏値図式の同型

概要：全ての元の語とその全作用に自然な圏値図式の同型を構成する。
方針：元の制限された語の作用と両関手の厳密な自然性を使う。
規約：空語・列の圧縮・恒等列の挿入を含む元の添字圏を使う。
使われ方：元の全語の nerve とその余極限の比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q) (Y : Paths Q)
  (β : (Quiver.FreeGroupoid.of Q).obj A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.obj Y)

def fiberCategoryDiagram : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ Cat.{max u v, max u v} where
  obj w := Cat.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueFiber A w Y β)
  map f := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberWordAction A Y β f).toCatHom
  map_id w := by apply Cat.Hom.ext; exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberWordAction_id A w
  map_comp f g := by apply Cat.Hom.ext; exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberWordAction_comp A f g

def coverCategoryDiagram : letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A; _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ Cat.{max u v, max u v} := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.categoryDiagram (⊤ : MorphismProperty (Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)))
    ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.root A))
    ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fiberEndpoint A Y β))

def fiberCategoryDiagramIso :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    fiberCategoryDiagram A Y β ≅ coverCategoryDiagram A Y β := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  exact NatIso.ofComponents (fun w => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberCategoryIso A w Y β) (by
    intro a b f
    apply Cat.Hom.ext
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLiftFunctor_wordAction A Y β f)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
