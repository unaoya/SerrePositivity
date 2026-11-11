module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverDiagramLift
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueMaps

/-!
# 元の全指定 zigzag の接頭射列による頂点のラベル

概要：元の各頂点へ根からの部分射列の値を割り当てる。
方針：既存の値の合成可能射列の最初からの射を使う。
規約：元の zigzag の始点と全頂点を保持する。
使われ方：元の全横列と縦射を被覆へ持ち上げる。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q]

lemma positiveEvaluation_inverts_top :
    (⊤ : MorphismProperty (Paths Q)).IsInvertedBy _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation := by
  intro x y f hf
  infer_instance

variable (A : Q) {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {Y : Paths Q}

def zigzagPrefix (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (⊤ : MorphismProperty (Paths Q)) w ((Paths.of Q).obj A) Y)
    (j : Fin (w.length + 1)) :
    (Quiver.FreeGroupoid.of Q).obj A ⟶ (Quiver.FreeGroupoid.of Q).obj (show Q from S.vertex j) :=
  eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.obj S.first.symm) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation positiveEvaluation_inverts_top S).map
      (homOfLE (Fin.zero_le j))

def zigzagVertex (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (⊤ : MorphismProperty (Paths Q)) w ((Paths.of Q).obj A) Y)
    (j : Fin (w.length + 1)) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A := ⟨S.vertex j, zigzagPrefix A S j⟩

lemma zigzagPrefix_first
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (⊤ : MorphismProperty (Paths Q)) w ((Paths.of Q).obj A) Y) :
    zigzagPrefix A S 0 = eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.obj S.first.symm) := by
  exact (congrArg (fun k => eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.obj S.first.symm) ≫ k)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation positiveEvaluation_inverts_top S).map_id _)).trans
      (Category.comp_id _)

lemma zigzagVertex_first
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (⊤ : MorphismProperty (Paths Q)) w ((Paths.of Q).obj A) Y) :
    zigzagVertex A S 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.root A := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Vertex.ext S.first
  exact (heq_of_eq (zigzagPrefix_first A S)).trans (eqToHom_heq_id_dom _ _ _)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
