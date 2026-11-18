module

public import Mathlib.CategoryTheory.WithTerminal.Basic
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
概要：有限被覆の脚の添字へ終点を加えたときの、包含の局所 comma の形を固定する。
方針：終点から脚への射は存在せず、脚自身では既存の完全忠実包含の恒等三角形を使う。
規約：HTT 4.3.2 の指定右 Kan 条件の局所形状の計算。新しい右 Kan 延長を仮定しない。
使われ方：S1 の extensive 層判定で、初対象の値の終対象性から星を除くための入力。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.InfinityCategories.Sheaves
variable (I : Type u) [SmallCategory I]

/-- 加えた終点から元の脚への三角形の圏は空。 -/
lemma extensiveTerminalComma_isEmpty :
    IsEmpty (StructuredArrow (WithTerminal.star : WithTerminal I)
      (WithTerminal.incl : I ⥤ WithTerminal I)) :=
  ⟨fun a => WithTerminal.false_of_from_star a.hom⟩

/-- 元の脚では、包含の恒等三角形が同じ局所 comma の初対象になる。 -/
def extensiveLegComma_isInitial (i : I) :
    IsInitial (StructuredArrow.mk (T := (WithTerminal.incl : I ⥤ WithTerminal I))
      (𝟙 (WithTerminal.of i))) :=
  StructuredArrow.mkIdInitial

end SerrePositivity.InfinityCategories.Sheaves
