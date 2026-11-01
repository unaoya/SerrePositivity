module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FreeQuiverCoverDiagramLift
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagValueMaps

/-!
# 元の全指定 zigzag の接頭射列による頂点のラベル

概要：元の各頂点へ根からの部分射列の値を割り当てる。
方針：既存の値の合成可能射列の最初からの射を使う。
規約：元の zigzag の始点と全頂点を保持する。
使われ方：元の全横列と縦射を被覆へ持ち上げる。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q]

lemma positiveEvaluation_inverts_top :
    (⊤ : MorphismProperty (Paths Q)).IsInvertedBy positiveEvaluation := by
  intro x y f hf
  infer_instance

variable (A : Q) {w : Word} {Y : Paths Q}

def zigzagPrefix (S : Zigzag (⊤ : MorphismProperty (Paths Q)) w ((Paths.of Q).obj A) Y)
    (j : Fin (w.length + 1)) :
    (Quiver.FreeGroupoid.of Q).obj A ⟶ (Quiver.FreeGroupoid.of Q).obj (show Q from S.vertex j) :=
  eqToHom (congrArg positiveEvaluation.obj S.first.symm) ≫
    (Zigzag.Value.path positiveEvaluation positiveEvaluation_inverts_top S).map
      (homOfLE (Fin.zero_le j))

def zigzagVertex (S : Zigzag (⊤ : MorphismProperty (Paths Q)) w ((Paths.of Q).obj A) Y)
    (j : Fin (w.length + 1)) : Vertex A := ⟨S.vertex j, zigzagPrefix A S j⟩

lemma zigzagPrefix_first
    (S : Zigzag (⊤ : MorphismProperty (Paths Q)) w ((Paths.of Q).obj A) Y) :
    zigzagPrefix A S 0 = eqToHom (congrArg positiveEvaluation.obj S.first.symm) := by
  exact (congrArg (fun k => eqToHom (congrArg positiveEvaluation.obj S.first.symm) ≫ k)
    ((Zigzag.Value.path positiveEvaluation positiveEvaluation_inverts_top S).map_id _)).trans
      (Category.comp_id _)

lemma zigzagVertex_first
    (S : Zigzag (⊤ : MorphismProperty (Paths Q)) w ((Paths.of Q).obj A) Y) :
    zigzagVertex A S 0 = root A := by
  apply Vertex.ext S.first
  exact (heq_of_eq (zigzagPrefix_first A S)).trans (eqToHom_heq_id_dom _ _ _)

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
