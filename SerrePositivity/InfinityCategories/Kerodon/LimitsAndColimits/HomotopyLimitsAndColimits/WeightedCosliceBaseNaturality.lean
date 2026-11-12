module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedCosliceComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveBaseChange

/-!
概要：元の weighted nerve と左 coslice の比較は添字の制限と厳密に可換である。
方針：射列を底の関手で写しても、元の cone simplex の対象と Hom は変わらない。
規約：係数を変更する自然変換とは区別し、通常の添字関手への自然性を述べる。
使われ方：G8 の要素の圏の比較を区間の両端へ制限する際の全単体での照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

variable {I J : Type u} [SmallCategory I] [SmallCategory J]
  {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 添字の関手で射列を写した cone simplex は、制限した図式の元の simplex と一致する。 -/
lemma weightedConeSimplex_base (H : J ⥤ I) (F : I ⥤ C) (x : C) {n : ℕ}
    (s : (weightedNerve (simplicialHomDiagram (H ⋙ F) x ⋙ SSet.opFunctor)) _⦋n⦌) :
    weightedConeSimplex F x
      ((weightedNerveBaseMap H (simplicialHomDiagram F x ⋙ SSet.opFunctor)).app _ s).2 =
    weightedConeSimplex (H ⋙ F) x s.2 := rfl

/-- 元の左 coslice の単体は、添字を制限しても同じ単体である。 -/
lemma weightedCosliceSimplex_base (H : J ⥤ I) (F : I ⥤ C) (x : C) {n : ℕ}
    (s : (weightedNerve (simplicialHomDiagram (H ⋙ F) x ⋙ SSet.opFunctor)) _⦋n⦌) :
    weightedCosliceSimplex F x
      ((weightedNerveBaseMap H (simplicialHomDiagram F x ⋙ SSet.opFunctor)).app _ s) =
    weightedCosliceSimplex (H ⋙ F) x s := rfl

/-- 元の左 coslice 比較の全写像は、weighted nerve の添字制限と厳密に可換である。 -/
lemma weightedCosliceComparison_base (H : J ⥤ I) (F : I ⥤ C) (x : C) :
    (SSet.uliftFunctor.{v, u}).map
        (weightedNerveBaseMap H (simplicialHomDiagram F x ⋙ SSet.opFunctor)) ≫
      weightedCosliceComparison F x = weightedCosliceComparison (H ⋙ F) x := rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
