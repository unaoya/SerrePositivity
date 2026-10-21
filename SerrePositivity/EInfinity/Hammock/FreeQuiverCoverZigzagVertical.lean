module

public import SerrePositivity.EInfinity.Hammock.FreeQuiverCoverZigzagLabels

/-!
# 元の全縦射に沿う接頭ラベルの整合

概要：元の固定語の全 zigzag の各位置を被覆上の図式へ持ち上げる。
方針：元の値の射列の自然変換と両端固定の条件を使う。
規約：全縦射を保持し、その元の射影を回収する。
使われ方：全 hammock 単体の縦方向の持ち上げ。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q) {w : Word} {Y : Paths Q}

lemma zigzagPrefix_naturality
    {S T : Zigzag (⊤ : MorphismProperty (Paths Q)) w ((Paths.of Q).obj A) Y}
    (f : S ⟶ T) (j : Fin (w.length + 1)) :
    zigzagPrefix A S j ≫ positiveEvaluation.map (f.app j) = zigzagPrefix A T j := by
  have h := (Zigzag.Value.pathMap positiveEvaluation positiveEvaluation_inverts_top f).naturality
    (homOfLE (Fin.zero_le j))
  change (Zigzag.Value.path positiveEvaluation positiveEvaluation_inverts_top S).map _ ≫
      positiveEvaluation.map (f.app j) = positiveEvaluation.map (f.app 0) ≫
        (Zigzag.Value.path positiveEvaluation positiveEvaluation_inverts_top T).map _ at h
  dsimp only [zigzagPrefix]
  rw [Category.assoc, h, ← Category.assoc, f.first, eqToHom_map, eqToHom_trans]

def zigzagColumnLabels (j : Fin (w.length + 1)) :
    DiagramLabels A (Zigzag.evaluation (W := (⊤ : MorphismProperty (Paths Q)))
      (X := (Paths.of Q).obj A) (Y := Y) j) where
  path S := zigzagPrefix A S j
  naturality f := zigzagPrefix_naturality A f j

def zigzagColumnLift (j : Fin (w.length + 1)) :
    letI := quiver A
    Zigzag (⊤ : MorphismProperty (Paths Q)) w ((Paths.of Q).obj A) Y ⥤ Paths (Vertex A) := by
  letI := quiver A
  exact diagramLift A (zigzagColumnLabels A j)

lemma zigzagColumnLift_projection (j : Fin (w.length + 1)) :
    letI := quiver A
    zigzagColumnLift A (Y := Y) j ⋙ pathProjection A = Zigzag.evaluation j := by
  let := quiver A
  exact diagramLift_projection A (zigzagColumnLabels A j)

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
