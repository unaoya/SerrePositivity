module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardRebuildArrows

/-!
# 元の全縦射の再構成と恒等図式の照合

概要：抽出したブロックを貼り直すと、元の全対象だけでなく全縦射も回収する。
方針：全頂点の成分を元の同じ縦射と照合し、関手の外延性で厳密に同定する。
規約：固定語の graph からの抽出・再構成を未証明の入力にしない。
使われ方：置換の counit を元の恒等図式へ接続する。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardRebuildMaps
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C] {n m : ℕ} {X Y : C}
  {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y}

lemma rebuilt_map_left (f : S ⟶ T) (i : Fin (n + 1)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rebuildFunctor.map f).app (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.leftVertex n m i))
      (f.app (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.leftVertex n m i)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rebuildFunctor, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyFunctor.zigzagFunctor, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyMaps.zigzagMap, _root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.leftVertex]
  apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_left_heq (b := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord m) _ _ _)
  apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_left_heq (b := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) _ _ _)
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryComparison, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map]
  apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_right_heq (a := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward)
    (b := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.forwardWord n) _ _ HEq.rfl i)
  rfl

lemma rebuilt_map_right (f : S ⟶ T) (i : Fin (m + 1)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rebuildFunctor.map f).app (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.rightVertex n m i))
      (f.app (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.rightVertex n m i)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rebuildFunctor, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyFunctor.zigzagFunctor, _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardFamilyMaps.zigzagMap, _root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.rightVertex]
  apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_right_heq
    (a := _root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.leftWithMiddle n) (b := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord m) _ _ ?_
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.forwardWord m) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) i))
  · dsimp only [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryComparison, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map]
    apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_left_heq (a := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.forwardWord m)
      (b := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) _ _ i)
    rfl
  · apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_right_heq (b := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward)
      _ _ ?_ (Fin.last 1))
    · exact (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryComparison_first (_root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Extract.rightPathMap f) (fun i => f.app_mem _)
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardExtractFamily.rightLeg.app S) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardExtractFamily.rightLeg.app T) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardExtractFamily.rightLeg_mem S) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardExtractFamily.rightLeg_mem T)
        (𝟙 Y) ((weakEquivalences C).id_mem _) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardExtractFamily.rightLeg.naturality f).symm).symm
    · exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryComparison_last _ _ _ _ _ _ _ _ _

lemma hom_first_heq_id {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {A B : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) w X Y}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Hom A B) : HEq (f.app 0) (𝟙 X) :=
  (conj_eqToHom_iff_heq _ _ A.first B.first).1 (by
    simpa only [Category.id_comp, eqToHom_trans] using f.first)

lemma hom_last_heq_id {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {A B : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) w X Y}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Hom A B) : HEq (f.app (Fin.last w.length)) (𝟙 Y) :=
  (conj_eqToHom_iff_heq _ _ A.last B.last).1 (by
    simpa only [Category.id_comp, eqToHom_trans] using f.last)

lemma rebuilt_map_app (f : S ⟶ T) (j : Fin ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m).length + 1)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rebuildFunctor.map f).app j) (f.app j) := by
  apply _root_.SerrePositivity.EInfinity.Hammock.MiddleBackward.Positions.vertex_cases n m
    (P := fun j => HEq ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rebuildFunctor.map f).app j) (f.app j))
  · exact (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardRebuildMaps.hom_first_heq_id (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rebuildFunctor.map f)).trans (hom_first_heq_id f).symm
  · exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardRebuildMaps.rebuilt_map_left f
  · exact rebuilt_map_right f
  · exact (hom_last_heq_id (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rebuildFunctor.map f)).trans (hom_last_heq_id f).symm

lemma rebuildFunctor_eq :
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rebuildFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y ⥤ _) = 𝟭 _ := by
  apply CategoryTheory.Functor.ext (F := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rebuildFunctor)
    (G := 𝟭 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y))
    (fun S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y => _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardRebuildArrows.rebuilt_eq S) ?_
  intro S T f
  apply (conj_eqToHom_iff_heq _ _ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardRebuildArrows.rebuilt_eq S) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardRebuildArrows.rebuilt_eq T)).2
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardRebuildArrows.rebuilt_eq S) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardRebuildArrows.rebuilt_eq T) _ f (rebuilt_map_app f)

def rebuildIso :
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rebuildFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y ⥤ _) ≅ 𝟭 _ :=
  eqToIso rebuildFunctor_eq

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardRebuildMaps
