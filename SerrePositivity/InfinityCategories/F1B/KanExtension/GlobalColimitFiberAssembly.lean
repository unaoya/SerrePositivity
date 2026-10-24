module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.GlobalColimitDiagram
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinFiberCocone
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCommaColimitDiagram

/-!
概要：点ごとの余極限から構成した相対 join の図式は実際に各 fiber で普遍余錐となる。
方針：相対始点境界充填を fiber の余錐の余極限性へ戻す。
規約：存在の仮定は指定された図式の各 fiber だけ。
使われ方：一般の左 Kan 拡張の点ごとの普遍性の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：指定された図式から各 fiber で余極限余錐となる相対 join の図式が存在する。
方針：相対始対象の族から構成した図式の境界充填を余極限性へ戻す。
規約：左端の図式を厳密に保つ。
使われ方：cocartesian な射影の場合の点ごとの Kan 拡張の候補。 -/
lemma exists_kanGlobalColimit_diagram_with_colimit_fibers {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [CocartesianFibration p]
    (F : K ⟶ D) (hcol : ∀ c : C _⦋0⦌, HasColimit (vertexFiberι p c ≫ F)) :
    ∃ H : relativeJoin p (𝟙 C) ⟶ D,
      relativeJoinInl p (𝟙 C) ≫ H = F ∧
        ∀ c : C _⦋0⦌, IsColimitCone (kanRelativeJoinFiberCocone p c H) := by
  obtain ⟨H, hH, hHi⟩ := exists_kanGlobalColimit_diagram p F hcol
  exact ⟨H, hH, fun c ↦ kanRelativeJoinFiberCocone_isColimit_of_initialBoundary p c H (hHi c)⟩

/-- 概要：任意の関手の局所余極限から各 fiber で普遍な comma の相対 join の図式が存在する。
方針：局所余極限から構成した図式の境界充填を各 fiber の余極限性へ戻す。
規約：元の関手の fibration 性は不要。
使われ方：coherent な左 Kan 拡張の候補の普遍性。 -/
lemma exists_kanLeftComma_diagram_with_colimit_fibers {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) (F₀ : K ⟶ D)
    (hcol : ∀ c : C _⦋0⦌, HasColimit (leftKanDiagram δ F₀ c)) :
    ∃ H : relativeJoin (kanLeftCommaProjection δ) (𝟙 C) ⟶ D,
      relativeJoinInl (kanLeftCommaProjection δ) (𝟙 C) ≫ H = kanLeftCommaSource δ ≫ F₀ ∧
        ∀ c : C _⦋0⦌,
          IsColimitCone (kanRelativeJoinFiberCocone (kanLeftCommaProjection δ) c H) := by
  obtain ⟨H, hH, hHi⟩ := exists_kanLeftComma_colimit_diagram δ F₀ hcol
  exact ⟨H, hH, fun c ↦ kanRelativeJoinFiberCocone_isColimit_of_initialBoundary
    (kanLeftCommaProjection δ) c H (hHi c)⟩

end SerrePositivity.InfinityCategories.F1B
