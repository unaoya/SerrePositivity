module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FreeQuiverCoverProjectedLabels

/-!
# 元の被覆頂点のラベルを射影の接頭値から回収する

概要：射影後の元の接頭射列の値は元の被覆頂点のラベルに一致する。
方針：固定根から始めて隣接列ごとに帰納する。
規約：逆向きの列でも元の同じ射を打ち消す。
使われ方：射影の値の回収と逆向きの持ち上げ。
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

lemma projectedPrefix_first :
    letI := quiver A
    ∀ Z : Zigzag (⊤ : MorphismProperty (Paths (Vertex A))) w
      ((Paths.of (Vertex A)).obj (root A))
      ((Paths.of (Vertex A)).obj (fiberEndpoint A Y β)),
      zigzagPrefix A ((zigzagProjection A w Y β).obj Z) 0 = (Z.vertex 0).path := by
  let := quiver A
  intro Z
  have hp : HEq (zigzagPrefix A ((zigzagProjection A w Y β).obj Z) 0)
      (𝟙 ((Quiver.FreeGroupoid.of Q).obj A)) :=
    (heq_of_eq (zigzagPrefix_first A _)).trans (eqToHom_heq_id_dom _ _ _)
  have hz := Vertex.path_heq A (show (show Vertex A from Z.vertex 0) = root A from Z.first)
  exact eq_of_heq (hp.trans hz.symm)

lemma projectedLabel_edge :
    letI := quiver A
    ∀ (Z : Zigzag (⊤ : MorphismProperty (Paths (Vertex A))) w
      ((Paths.of (Vertex A)).obj (root A))
      ((Paths.of (Vertex A)).obj (fiberEndpoint A Y β))) (i : Fin w.length),
      (Z.vertex i.castSucc).path ≫ Zigzag.Value.edge positiveEvaluation
        positiveEvaluation_inverts_top ((zigzagProjection A w Y β).obj Z) i =
          (Z.vertex i.succ).path := by
  let := quiver A
  intro Z i
  cases hi : w.direction i with
  | forward =>
    rw [Zigzag.Value.edge_forward _ _ _ i hi]
    exact projected_forward_label A Z i hi
  | backward =>
    rw [Zigzag.Value.edge_backward _ _ _ i hi]
    have h := projected_backward_label A Z i hi
    let e := Zigzag.Value.backwardIso positiveEvaluation positiveEvaluation_inverts_top
      ((zigzagProjection A w Y β).obj Z) i hi
    change (Z.vertex i.succ).path ≫ e.hom = (Z.vertex i.castSucc).path at h
    have hc := congrArg (fun p => p ≫ e.inv) h
    have hc' : (Z.vertex i.succ).path = (Z.vertex i.castSucc).path ≫ e.inv := by
      simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hc
    exact hc'.symm

lemma projectedPrefix_eq_label :
    letI := quiver A
    ∀ (Z : Zigzag (⊤ : MorphismProperty (Paths (Vertex A))) w
      ((Paths.of (Vertex A)).obj (root A))
      ((Paths.of (Vertex A)).obj (fiberEndpoint A Y β))) (j : Fin (w.length + 1)),
      zigzagPrefix A ((zigzagProjection A w Y β).obj Z) j = (Z.vertex j).path := by
  let := quiver A
  intro Z j
  induction j using Fin.induction with
  | zero => exact projectedPrefix_first A Z
  | succ i ih =>
    have h := zigzagPrefix_edge A ((zigzagProjection A w Y β).obj Z) i
    rw [ih] at h
    exact h.symm.trans (projectedLabel_edge A Z i)

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
