module

public import SerrePositivity.InfinityCategories.F2.StrictKanPullbackMapEquivalence
public import SerrePositivity.InfinityCategories.F2.IntervalReplacementSection
public import SerrePositivity.InfinityCategories.F1B.WeakWhitehead

/-!
概要：元の interval 引き戻しを、両脚を置換した同じ cospan の引き戻しへ比較する。
方針：第二脚の定値切断と恒等成分で厳密な比較を作り、成分ごとの同値性を使う。
規約：元の比較射を明示。使われ方：native 値と Kan 模型を同じ引き戻しへ送る。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
variable {X Y Z : SSet.{u}} [KanComplex X] [KanComplex Y] [KanComplex Z]
  (f : X ⟶ Z) (g : Y ⟶ Z)

/-- 元の二入力を保持して、第二脚も interval で置換した引き戻しへ送る比較。 -/
def intervalPullbackDoubleReplacementComparison : intervalPullback f g ⟶
    pullback (intervalReplacementEndpoint f) (intervalReplacementEndpoint g) :=
  pullback.map (intervalReplacementEndpoint f) g
    (intervalReplacementEndpoint f) (intervalReplacementEndpoint g)
    (𝟙 _) (intervalReplacementSection g) (𝟙 _)
    (by simp only [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, intervalReplacementSection_endpoint])

/-- 第二脚の同じ定値切断から作った引き戻し比較自体がホモトピー同値。 -/
lemma intervalPullbackDoubleReplacementComparison_homotopyEquivalence :
    IsSimplicialHomotopyEquivalence (intervalPullbackDoubleReplacementComparison f g) := by
  apply strictKanPullbackMap_homotopyEquivalence
    (intervalReplacementEndpoint f) g (intervalReplacementEndpoint f)
    (intervalReplacementEndpoint g) (𝟙 _) (intervalReplacementSection g) (𝟙 Z)
    (by simp only [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, intervalReplacementSection_endpoint])
  · exact HomotopyLimits.homotopyEquivalence_of_isIso (𝟙 (intervalReplacement f))
  · have h := intervalReplacementSection_isWeakHomotopyEquivalence g
    exact h.isSimplicialHomotopyEquivalence
  · exact HomotopyLimits.homotopyEquivalence_of_isIso (𝟙 Z)

end SerrePositivity.InfinityCategories.F2
