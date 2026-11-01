module

public import SerrePositivity.InfinityCategories.ModelBridge.MiddleBackwardRebuildArrows

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
namespace SerrePositivity.EInfinity.Hammock.MiddleBackward.Extract
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra ForwardPath

variable {C : Type u} [Category.{v} C] [ModelCategory C] {n m : ℕ} {X Y : C}
  {S T : Zigzag (weakEquivalences C) (word n m) X Y}

lemma rebuilt_map_left (f : S ⟶ T) (i : Fin (n + 1)) :
    HEq ((rebuildFunctor.map f).app (Positions.leftVertex n m i))
      (f.app (Positions.leftVertex n m i)) := by
  dsimp only [rebuildFunctor, Family.zigzagFunctor, Family.zigzagMap, Positions.leftVertex]
  apply HEq.trans (ZigzagAppend.Moving.app_left_heq (b := rightBoundaryWord m) _ _ _)
  apply HEq.trans (ZigzagAppend.Moving.app_left_heq (b := Word.single .backward) _ _ _)
  dsimp only [leftBoundaryComparison, ZigzagAppend.Moving.map]
  apply HEq.trans (ZigzagAppend.Moving.app_right_heq (a := Word.single .backward)
    (b := forwardWord n) _ _ HEq.rfl i)
  rfl

lemma rebuilt_map_right (f : S ⟶ T) (i : Fin (m + 1)) :
    HEq ((rebuildFunctor.map f).app (Positions.rightVertex n m i))
      (f.app (Positions.rightVertex n m i)) := by
  dsimp only [rebuildFunctor, Family.zigzagFunctor, Family.zigzagMap, Positions.rightVertex]
  apply HEq.trans (ZigzagAppend.Moving.app_right_heq
    (a := Positions.leftWithMiddle n) (b := rightBoundaryWord m) _ _ ?_
    (Word.leftVertex (forwardWord m) (Word.single .backward) i))
  · dsimp only [rightBoundaryComparison, ZigzagAppend.Moving.map]
    apply HEq.trans (ZigzagAppend.Moving.app_left_heq (a := forwardWord m)
      (b := Word.single .backward) _ _ i)
    rfl
  · apply HEq.trans (ZigzagAppend.Moving.app_right_heq (b := Word.single .backward)
      _ _ ?_ (Fin.last 1))
    · exact (rightBoundaryComparison_first (rightPathMap f) (fun i => f.app_mem _)
        (rightLeg.app S) (rightLeg.app T) (rightLeg_mem S) (rightLeg_mem T)
        (𝟙 Y) ((weakEquivalences C).id_mem _) (rightLeg.naturality f).symm).symm
    · exact leftBoundaryComparison_last _ _ _ _ _ _ _ _ _

lemma hom_first_heq_id {w : Word} {A B : Zigzag (weakEquivalences C) w X Y}
    (f : Zigzag.Hom A B) : HEq (f.app 0) (𝟙 X) :=
  (conj_eqToHom_iff_heq _ _ A.first B.first).1 (by
    simpa only [Category.id_comp, eqToHom_trans] using f.first)

lemma hom_last_heq_id {w : Word} {A B : Zigzag (weakEquivalences C) w X Y}
    (f : Zigzag.Hom A B) : HEq (f.app (Fin.last w.length)) (𝟙 Y) :=
  (conj_eqToHom_iff_heq _ _ A.last B.last).1 (by
    simpa only [Category.id_comp, eqToHom_trans] using f.last)

lemma rebuilt_map_app (f : S ⟶ T) (j : Fin ((word n m).length + 1)) :
    HEq ((rebuildFunctor.map f).app j) (f.app j) := by
  apply Positions.vertex_cases n m
    (P := fun j => HEq ((rebuildFunctor.map f).app j) (f.app j))
  · exact (hom_first_heq_id (rebuildFunctor.map f)).trans (hom_first_heq_id f).symm
  · exact rebuilt_map_left f
  · exact rebuilt_map_right f
  · exact (hom_last_heq_id (rebuildFunctor.map f)).trans (hom_last_heq_id f).symm

lemma rebuildFunctor_eq :
    (rebuildFunctor : Zigzag (weakEquivalences C) (word n m) X Y ⥤ _) = 𝟭 _ := by
  apply CategoryTheory.Functor.ext (F := rebuildFunctor)
    (G := 𝟭 (Zigzag (weakEquivalences C) (word n m) X Y))
    (fun S : Zigzag (weakEquivalences C) (word n m) X Y => rebuilt_eq S) ?_
  intro S T f
  apply (conj_eqToHom_iff_heq _ _ (rebuilt_eq S) (rebuilt_eq T)).2
  exact Zigzag.hom_hext (rebuilt_eq S) (rebuilt_eq T) _ f (rebuilt_map_app f)

def rebuildIso :
    (rebuildFunctor : Zigzag (weakEquivalences C) (word n m) X Y ⥤ _) ≅ 𝟭 _ :=
  eqToIso rebuildFunctor_eq

end SerrePositivity.EInfinity.Hammock.MiddleBackward.Extract
