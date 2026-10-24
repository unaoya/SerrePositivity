module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.GlobalColimitDiagram
public import SerrePositivity.InfinityCategories.F1B.KanExtension.CommaLocalColimits

/-!
概要：任意の関手の局所余極限から oriented comma の相対 join の図式を構成する。
方針：局所添字の余極限を comma fiber へ移し、cocartesian な射影の存在定理を適用する。
規約：元の関手に fibration 性を要求しない。
使われ方：点ごとの左 Kan 拡張の coherent な候補の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：任意の δ の局所余極限は oriented comma の相対 join 上へ coherent に組み立てられる。
方針：fiber の余極限の存在の比較を全頂点で使い、大域図式の存在定理を適用する。
規約：左端の図式を厳密に保ち、各頂点で相対始対象性を保証する。
使われ方：左 Kan 拡張の指定変換を取り出すための相対 join の図式。 -/
lemma exists_kanLeftComma_colimit_diagram {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) (F₀ : K ⟶ D)
    (hcol : ∀ c : C _⦋0⦌, HasColimit (leftKanDiagram δ F₀ c)) :
    ∃ H : relativeJoin (kanLeftCommaProjection δ) (𝟙 C) ⟶ D,
      relativeJoinInl (kanLeftCommaProjection δ) (𝟙 C) ≫ H = kanLeftCommaSource δ ≫ F₀ ∧
        ∀ c : C _⦋0⦌, InitialBoundaryLifting
          (SerrePositivity.InfinityCategories.fiberwiseHomPre (D := D) (kanRelativeJoinInlOver (kanLeftCommaProjection δ)))
            ((kanGlobalDiagramFamily
              (relativeJoinBaseProjection (kanLeftCommaProjection δ) (𝟙 C)) H).app
                (Opposite.op ⦋0⦌) c) := by
  apply exists_kanGlobalColimit_diagram (kanLeftCommaProjection δ) (kanLeftCommaSource δ ≫ F₀)
  intro c
  exact (kanLeftCommaFiber_hasColimit_iff_local δ F₀ c).2 (hcol c)

end SerrePositivity.InfinityCategories.F1B
