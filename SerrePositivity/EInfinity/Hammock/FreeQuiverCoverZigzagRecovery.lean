module

public import SerrePositivity.EInfinity.Hammock.FreeQuiverCoverFiberProjection

/-!
# 持ち上げと射影の両向きの対象の回収

概要：被覆の元の全頂点・全列と値の fiber の元の対象を回収する。
方針：接頭ラベルの回収と正向き射影の忠実性を使う。
規約：列の長さや向きを変更しない。
使われ方：固定語ごとの両関手の合成の等式。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q)

lemma pathProjection_hom_hext :
    letI := quiver A
    ∀ {x y x' y' : Paths (Vertex A)} (_ : x = x') (_ : y = y')
      (p : x ⟶ y) (q : x' ⟶ y'),
      HEq ((pathProjection A).map p) ((pathProjection A).map q) → HEq p q := by
  let := quiver A
  let := pathProjection_faithful A
  intro x y x' y' hx hy p q hp
  cases hx
  cases hy
  exact heq_of_eq ((pathProjection A).map_injective (eq_of_heq hp))

variable {w : Word} {Y : Paths Q}
  {β : (Quiver.FreeGroupoid.of Q).obj A ⟶ positiveEvaluation.obj Y}

lemma zigzagVertex_projected_eq :
    letI := quiver A
    ∀ (Z : Zigzag (⊤ : MorphismProperty (Paths (Vertex A))) w
      ((Paths.of (Vertex A)).obj (root A))
      ((Paths.of (Vertex A)).obj (fiberEndpoint A Y β))) (j : Fin (w.length + 1)),
      zigzagVertex A ((zigzagProjection A w Y β).obj Z) j =
        (show Vertex A from Z.vertex j) := by
  let := quiver A
  intro Z j
  exact Vertex.ext rfl (heq_of_eq (projectedPrefix_eq_label A Z j))

lemma zigzagLift_fiberProjection_obj :
    letI := quiver A
    ∀ Z : Zigzag (⊤ : MorphismProperty (Paths (Vertex A))) w
      ((Paths.of (Vertex A)).obj (root A))
      ((Paths.of (Vertex A)).obj (fiberEndpoint A Y β)),
      zigzagLift A ((zigzagFiberProjection A w Y β).obj Z) = Z := by
  let := quiver A
  intro Z
  have hv : ∀ j, (zigzagLift A ((zigzagFiberProjection A w Y β).obj Z)).vertex j =
      Z.vertex j := fun j =>
    congrArg (Paths.of (Vertex A)).obj (zigzagVertex_projected_eq A Z j)
  apply Zigzag.object_ext _ _ hv
  intro i
  exact pathProjection_hom_hext A (hv _) (hv _) _ _
    (heq_of_eq (zigzagLift_arrow_projection A ((zigzagFiberProjection A w Y β).obj Z) i))

lemma zigzagFiberProjection_lift_obj (S : ZigzagValueFiber A w Y β) :
    letI := quiver A
    (zigzagFiberProjection A w Y β).obj (zigzagLift A S) = S := by
  let := quiver A
  apply ObjectProperty.FullSubcategory.ext
  exact zigzagLift_projection A S

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
