module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.RootedFiniteCategoryLaws
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FiniteQuiverPathRelative
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FiniteQuiverProjectionEmbedding

/-!
# 元の有限包から全体への固定端点の射影

概要：各有限包から全体への元の包含が全ての有限部分集合の遷移と可換となる。
方針：元の自由関手の射影の等式を固定端点の相対関手へ移す。
規約：元の各行・全縦射と同じ全体への射影を使う。
使われ方：全被覆への余錐と全次数の単射性。
-/

@[expose] public section
universe u v w w'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.RootedFinite
open CategoryTheory
attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] (T : WideSubquiver (Quiver.Symmetrify Q))
  [Quiver.Arborescence T] (X Y : Q)

def projectionFunctor (a : Word) (S : Finset Q) : termCategory T X Y a S ⥤
    Zigzag (⊤ : MorphismProperty (Paths Q)) a ((Paths.of Q).obj X) ((Paths.of Q).obj Y) := by
  letI := FiniteQuiver.quiver (hull T X Y S)
  exact Zigzag.Relative.fixedFunctor (FiniteQuiver.pathRelative (hull T X Y S)) rfl rfl

lemma mapFunctor_projection (a : Word) {S R : Finset Q} (h : S ⊆ R) :
    mapFunctor T X Y a h ⋙ projectionFunctor T X Y a R = projectionFunctor T X Y a S := by
  let := FiniteQuiver.quiver (hull T X Y S)
  let := FiniteQuiver.quiver (hull T X Y R)
  let F := FiniteQuiver.subsetRelative (QuiverTree.endpointHull_mono T X Y h)
  let G := FiniteQuiver.pathRelative (hull T X Y R)
  calc
    _ = Zigzag.Relative.fixedFunctor (F.comp G) rfl rfl :=
      (Zigzag.Relative.fixedFunctor_comp F G rfl rfl rfl rfl).symm
    _ = _ := Zigzag.Relative.fixedFunctor_congr
      (F := F.comp G) (G := FiniteQuiver.pathRelative (hull T X Y S)) (w := a)
      (FiniteQuiver.subsetFunctor_pathInclusion (QuiverTree.endpointHull_mono T X Y h))
        rfl rfl rfl rfl

lemma projectionFunctor_obj_injective (a : Word) (S : Finset Q) :
    Function.Injective (projectionFunctor T X Y a S).obj := by
  let := FiniteQuiver.quiver (hull T X Y S)
  exact FiniteQuiver.zigzagProjection_obj_injective (hull T X Y S) a _ _

lemma projectionFunctor_faithful (a : Word) (S : Finset Q) :
    (projectionFunctor T X Y a S).Faithful := by
  let := FiniteQuiver.quiver (hull T X Y S)
  exact FiniteQuiver.zigzagProjection_faithful (hull T X Y S) a _ _

lemma projection_nerve_injective (a : Word) (S : Finset Q) (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((nerveMap (projectionFunctor T X Y a S)).app n) := by
  let := FiniteQuiver.quiver (hull T X Y S)
  exact FiniteQuiver.graphProjection_injective (hull T X Y S) a n _ _

end SerrePositivity.EInfinity.Hammock.RootedFinite
