module

public import SerrePositivity.EInfinity.Hammock.UnmarkedCutValueRecovery

/-!
# 元の切断の残りの文字列と長さの厳密な減少

概要：実際の非空 hammock の切断の残りは元の文字列の tail であり、長さが一減る。
方針：同じ切断射の文字列回収式を各次数の点へ評価する。
規約：元の非空部分の任意の点を扱い、表示を選び直さない。
使われ方：長さによる well-founded な切断の反復。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) {X Y : Paths C}
  {n : SimplexCategoryᵒᵖ} (x : (NonemptyValue.space W X Y).obj n)

lemma nonemptyCut_value :
    (colimitValue W X Y).app n x.val =
      ((nonemptyCut W X Y).app n x).1.val ::
        (colimitValue W ((nonemptyCut W X Y).app n x).1.val.right Y).app n
          ((nonemptyCut W X Y).app n x).2.2 :=
  (congrArg (fun k => k.app n x) (nonemptyCut_wordValue W X Y)).symm

lemma nonemptyCut_generator :
    ((colimitValue W X Y).app n x.val).head? =
      some ((nonemptyCut W X Y).app n x).1.val := by
  rw [nonemptyCut_value W x]
  rfl

lemma nonemptyCut_residual_tail :
    (colimitValue W ((nonemptyCut W X Y).app n x).1.val.right Y).app n
      ((nonemptyCut W X Y).app n x).2.2 = ((colimitValue W X Y).app n x.val).tail := by
  rw [nonemptyCut_value W x]
  rfl

lemma nonemptyCut_residual_length :
    ((colimitValue W X Y).app n x.val).length =
      ((colimitValue W ((nonemptyCut W X Y).app n x).1.val.right Y).app n
        ((nonemptyCut W X Y).app n x).2.2).length + 1 :=
  congrArg List.length (nonemptyCut_value W x)

lemma nonemptyCut_residual_length_lt :
    ((colimitValue W ((nonemptyCut W X Y).app n x).1.val.right Y).app n
      ((nonemptyCut W X Y).app n x).2.2).length < ((colimitValue W X Y).app n x.val).length := by
  rw [nonemptyCut_residual_length W x]
  exact Nat.lt_succ_self _

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor
