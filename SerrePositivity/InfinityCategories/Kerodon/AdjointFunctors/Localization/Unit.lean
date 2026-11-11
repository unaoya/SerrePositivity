module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitGraph
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# 空語による元の hammock の単位射

概要：恒等端点の空語の zigzag から、固定語の graph と全語の余極限への単位を構成。
方針：空語の同じ一頂点を全次数の定値射列として使う。
規約：合成に対する左右単位則は後続。単位射の全作用素での自然性は構成済み。
使われ方：全語の余極限上の豊穣圏の単位。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

/-- 元の一頂点だけを持つ空語の zigzag。 -/
def emptyObj (X : C) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty X X where
  vertex _ := X
  first := rfl
  last := rfl
  arrow i := Fin.elim0 i
  backward_mem i := Fin.elim0 i

/-- 全次数で同じ空語の対象を使う、元の単体的単位。 -/
def graphUnit [W.IsMultiplicative] (X : C) : 𝟙_ SSet.{max u v} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty X X where
  app n := ↾fun _ => (Functor.const (Fin (n.unop.len + 1))).obj (emptyObj W X)
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro _
    rfl

/-- 全語の余極限への、同じ元の空語による単位射。 -/
def colimitUnit [W.IsMultiplicative] (X : C) : 𝟙_ SSet.{max u v} ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X X :=
  graphUnit W X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X X _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty

/-- 全単体の全頂点で、元の同じ空語の一頂点だけを使う。 -/
lemma graphUnit_vertex [W.IsMultiplicative] (X : C) (n : SimplexCategoryᵒᵖ)
    (x : (𝟙_ SSet.{max u v}).obj n) (j : Fin (n.unop.len + 1)) :
    ((graphUnit W X).app n x).obj j = emptyObj W X := rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
