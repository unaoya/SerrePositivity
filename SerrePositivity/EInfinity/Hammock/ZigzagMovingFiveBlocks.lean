module

public import SerrePositivity.EInfinity.Hammock.ZigzagMovingAppendAssociativity
public import SerrePositivity.EInfinity.Hammock.ZigzagMovingAppendNaturality
public import SerrePositivity.EInfinity.Hammock.ZigzagMovingWordActionLaws

/-!
# 元の五ブロックの括弧を保つ内部圧縮

概要：前後の語を保持して内部三ブロックを圧縮する、元の語の射を構成する。
方針：全図式の結合則で三ブロックをまとめ、元の appendMap を適用する。
規約：元の ((前・左)・中央)・(右・後) の括弧から始める。
使われ方：内部切断の refinedDiagram 全体の回収。
-/

@[expose] public section
universe u v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Word
open CategoryTheory

lemma fiveBlocks_rebracket (a b c d e : Word) :
    append (append (append a b) c) (append d e) =
      append (append a (append (append b c) d)) e := by
  simp only [append_assoc]

def fiveBlocksMap {a b c d e k : Word} (f : append (append b c) d ⟶ k) :
    append (append (append a b) c) (append d e) ⟶ append (append a k) e :=
  eqToHom (fiveBlocks_rebracket a b c d e) ≫ appendMap (appendMap (𝟙 a) f) (𝟙 e)

end SerrePositivity.EInfinity.Hammock.Word
namespace SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram
open CategoryTheory

variable {D : Type uD} [Category.{vD} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative]
  {a a' b b' c d e k : Word} {A B E L M N : D ⥤ C}

lemma append_heq (ha : a = a') (hb : b = b')
    {F : MovingDiagram D C W a A B} {F' : MovingDiagram D C W a' A B}
    {G : MovingDiagram D C W b B E} {G' : MovingDiagram D C W b' B E}
    (hF : HEq F F') (hG : HEq G G') : HEq (F.append G) (F'.append G') := by
  cases ha
  cases hb
  cases hF
  cases hG
  rfl

lemma append_assoc_heq (F : MovingDiagram D C W a A B)
    (G : MovingDiagram D C W b B E) (H : MovingDiagram D C W c E L) :
    HEq ((F.append G).append H) (F.append (G.append H)) :=
  (changeWord_heq (Word.append_assoc a b c) _).symm.trans
    (heq_of_eq (changeWord_append_assoc F G H))

lemma fiveBlocks_rebracket (P : MovingDiagram D C W a A B)
    (F : MovingDiagram D C W b B E) (G : MovingDiagram D C W c E L)
    (H : MovingDiagram D C W d L M) (Q : MovingDiagram D C W e M N) :
    changeWord (Word.fiveBlocks_rebracket a b c d e)
      (((P.append F).append G).append (H.append Q)) =
        (P.append ((F.append G).append H)).append Q := by
  apply changeWord_eq_of_heq
  exact (append_heq (Word.append_assoc a b c) rfl (append_assoc_heq P F G) HEq.rfl).trans
    ((append_assoc_heq (P.append (F.append G)) H Q).symm.trans
      (append_heq (Word.append_assoc a (Word.append b c) d) rfl
        (append_assoc_heq P (F.append G) H) HEq.rfl))

lemma wordAction_fiveBlocks (f : Word.append (Word.append b c) d ⟶ k)
    (P : MovingDiagram D C W a A B) (F : MovingDiagram D C W b B E)
    (G : MovingDiagram D C W c E L) (H : MovingDiagram D C W d L M)
    (Q : MovingDiagram D C W e M N) :
    wordAction (Word.fiveBlocksMap f) (((P.append F).append G).append (H.append Q)) =
      (P.append (wordAction f ((F.append G).append H))).append Q := by
  rw [Word.fiveBlocksMap, wordAction_comp, wordAction_eqToHom, fiveBlocks_rebracket,
    wordAction_append, wordAction_append, wordAction_id, wordAction_id]

end SerrePositivity.EInfinity.Hammock.Zigzag.MovingDiagram
