module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverZigzagLabels

/-!
# 元の全縦射に沿う接頭ラベルの整合

概要：元の固定語の全 zigzag の各位置を被覆上の図式へ持ち上げる。
方針：元の値の射列の自然変換と両端固定の条件を使う。
規約：全縦射を保持し、その元の射影を回収する。
使われ方：全 hammock 単体の縦方向の持ち上げ。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q) {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {Y : Paths Q}

lemma zigzagPrefix_naturality
    {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (⊤ : MorphismProperty (Paths Q)) w ((Paths.of Q).obj A) Y}
    (f : S ⟶ T) (j : Fin (w.length + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagPrefix A S j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.map (f.app j) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagPrefix A T j := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathMap _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation_inverts_top f).naturality
    (homOfLE (Fin.zero_le j))
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation_inverts_top S).map _ ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.map (f.app j) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.map (f.app 0) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation_inverts_top T).map _ at h
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagPrefix]
  rw [Category.assoc, h, ← Category.assoc, f.first, eqToHom_map, eqToHom_trans]

def zigzagColumnLabels (j : Fin (w.length + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DiagramLabels A (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.evaluation (W := (⊤ : MorphismProperty (Paths Q)))
      (X := (Paths.of Q).obj A) (Y := Y) j) where
  path S := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagPrefix A S j
  naturality f := zigzagPrefix_naturality A f j

def zigzagColumnLift (j : Fin (w.length + 1)) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (⊤ : MorphismProperty (Paths Q)) w ((Paths.of Q).obj A) Y ⥤ Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagramLift A (zigzagColumnLabels A j)

lemma zigzagColumnLift_projection (j : Fin (w.length + 1)) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
    zigzagColumnLift A (Y := Y) j ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathProjection A = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.evaluation j := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.quiver A
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagramLift_projection A (zigzagColumnLabels A j)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
