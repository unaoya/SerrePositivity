module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverFiberProjection

/-!
# 持ち上げと射影の両向きの対象の回収

概要：被覆の元の全頂点・全列と値の fiber の元の対象を回収する。
方針：接頭ラベルの回収と正向き射影の忠実性を使う。
規約：列の長さや向きを変更しない。
使われ方：固定語ごとの両関手の合成の等式。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q)

lemma pathProjection_hom_hext :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ {x y x' y' : Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)} (_ : x = x') (_ : y = y')
      (p : x ⟶ y) (q : x' ⟶ y'),
      HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathProjection A).map p) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathProjection A).map q) → HEq p q := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathProjection_faithful A
  intro x y x' y' hx hy p q hp
  cases hx
  cases hy
  exact heq_of_eq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathProjection A).map_injective (eq_of_heq hp))

variable {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {Y : Paths Q}
  {β : (Quiver.FreeGroupoid.of Q).obj A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.obj Y}

lemma zigzagVertex_projected_eq :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ (Z : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (⊤ : MorphismProperty (Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A))) w
      ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.root A))
      ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fiberEndpoint A Y β))) (j : Fin (w.length + 1)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagVertex A ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagProjection A w Y β).obj Z) j =
        (show _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A from Z.vertex j) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  intro Z j
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Vertex.ext rfl (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.projectedPrefix_eq_label A Z j))

lemma zigzagLift_fiberProjection_obj :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    ∀ Z : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (⊤ : MorphismProperty (Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A))) w
      ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.root A))
      ((Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fiberEndpoint A Y β)),
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLift A ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberProjection A w Y β).obj Z) = Z := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  intro Z
  have hv : ∀ j, (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLift A ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberProjection A w Y β).obj Z)).vertex j =
      Z.vertex j := fun j =>
    congrArg (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A)).obj (zigzagVertex_projected_eq A Z j)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext _ _ hv
  intro i
  exact pathProjection_hom_hext A (hv _) (hv _) _ _
    (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLift_arrow_projection A ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberProjection A w Y β).obj Z) i))

lemma zigzagFiberProjection_lift_obj (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueFiber A w Y β) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagFiberProjection A w Y β).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLift A S) = S := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  apply ObjectProperty.FullSubcategory.ext
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagLift_projection A S

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
