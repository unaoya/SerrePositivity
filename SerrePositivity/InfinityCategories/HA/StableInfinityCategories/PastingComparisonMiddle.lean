module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PastingComparisonHomotopy

/-! # 貼り合わせ比較の中間成分

概要：左四角形から外側への変形の右下の道は右四角形の下辺である。
方針：形状を頂点で計算して、指定長方形へ後合成する。
規約：値域に追加の仮定なし。使われ方：合成射の cofiber 比較の第二成分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：比較形状の右下の道は長方形の下辺の後半となる。
方針：有限頂点の座標を計算する。
規約：実際の単体的な射の等号。使われ方：第二成分の道の計算。 -/
lemma pastingLeftToOuterShape_middle :
    ((stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftToOuterShape = snd Δ[0] Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫
        (stdSimplex.δ (0 : Fin 3) ▷ Δ[1]) := by
  apply CartesianMonoidalCategory.hom_ext
  all_goals
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
    apply ConcreteCategory.hom_ext
    rintro ⟨p, q⟩
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective p
    obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective q
    fin_cases i
    fin_cases j <;> rfl

/-- 概要：比較ホモトピーの右下の道は右四角形の下辺。
方針：形状の道の式を長方形で評価する。
規約：普遍性は不要。使われ方：三角形の射の第二成分を指定射に照合する。 -/
lemma pastingLeftToOuterHomotopy_middle {X : SSet.{u}}
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    ((stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge) ▷ (Δ[1] : SSet.{u})) ≫
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftToOuterHomotopy F).h =
        snd Δ[0] Δ[1] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 0) := by
  change _ ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingLeftToOuterShape ≫ F) = _
  rw [← Category.assoc, pastingLeftToOuterShape_middle]
  rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
