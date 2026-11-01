module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagAppendAssociativity
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.GraphComposition
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.Diagram

/-!
# 固定語の graph の元の合成の結合則

概要：三つの固定語の元の合成は、語の結合遷移の後で結合的。
方針：全単体の全対象・全縦射を三重連結の照合で比較する。
規約：元の全次数を保持し、π₀ の比較で代用しない。
使われ方：実際の全語の余極限上の合成の結合則。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (a b c : Word) (X Y Z V : C)

lemma graphComposition_assoc :
    (graphComposition W a b X Y Z ⊗ₘ 𝟙 (graph W c Z V)) ≫
        graphComposition W (Word.append a b) c X Z V ≫
          (graphDiagram W X V).map (eqToHom (Word.append_assoc a b c)) =
      (α_ (graph W a X Y) (graph W b Y Z) (graph W c Z V)).hom ≫
        (𝟙 (graph W a X Y) ⊗ₘ graphComposition W b c Y Z V) ≫
          graphComposition W a (Word.append b c) X Y V := by
  rw [graphDiagram_map]
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro p
  change (p.1.1.prod' p.1.2 ⋙ ZigzagAppend.functor).prod' p.2 ⋙ ZigzagAppend.functor ⋙
      WordAction.functor (eqToHom (Word.append_assoc a b c)) =
    p.1.1.prod' (p.1.2.prod' p.2 ⋙ ZigzagAppend.functor) ⋙ ZigzagAppend.functor
  apply Functor.hext (fun j => eq_of_heq ((WordAction.obj_eqToHom_heq _ _).trans
    (ZigzagAppend.obj_assoc_heq (p.1.1.obj j) (p.1.2.obj j) (p.2.obj j))))
  intro i j f
  exact (WordAction.map_eqToHom_heq _ _).trans
    (ZigzagAppend.map_assoc_heq (p.1.1.map f) (p.1.2.map f) (p.2.map f))

end SerrePositivity.EInfinity.Hammock
