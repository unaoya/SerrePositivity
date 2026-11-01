module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedAttachedPrefix
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.MarkedZigzagLift

/-!
# 固定生成矢の始域までの実際の W-hammock

概要：最初の非指定生成矢までの prefix の全行を、元の指定部分圏の hammock に回収する。
方針：証明済みの全列・全縦射の所属と元の包含への回収式を使う。
規約：元の指定部分圏を使い、弱比較や自然性を入力にしない。
使われ方：元の hammock の自由積分解の最初の因子。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.AttachedPrefix
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (τ : (graph W.paths w X Y).obj n) (h0 : ∃ j, column W (τ.obj 0) j ≠ [])

def markedFunctor := MarkedZigzag.liftFunctor W.paths (functor W τ h0) (arrow_mem W τ h0)

lemma markedFunctor_inclusion :
    markedFunctor W τ h0 ⋙ Zigzag.Relative.functor (MarkedZigzag.inclusion W.paths) =
      functor W τ h0 := MarkedZigzag.liftFunctor_inclusion W.paths _ _

def markedSimplex :
    (graph (⊤ : MorphismProperty (WideSubcategory W.paths))
      (Word.append (Word.ColumnSplit.before w (index W τ h0)) (Word.single .forward))
      (⟨X⟩ : WideSubcategory W.paths)
      (⟨(rowGenerator W τ (index W τ h0) (nonempty W τ h0)).left⟩ :
        WideSubcategory W.paths)).obj n := markedFunctor W τ h0

lemma markedSimplex_inclusion :
    (nerveMap (Zigzag.Relative.functor (MarkedZigzag.inclusion W.paths))).app n
      (markedSimplex W τ h0) = functor W τ h0 := markedFunctor_inclusion W τ h0

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.AttachedPrefix
