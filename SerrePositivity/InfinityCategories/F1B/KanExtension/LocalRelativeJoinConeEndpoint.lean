module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinFiberLift
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LocalRelativeJoinConeComparison

/-!
概要：局所余錐の比較の終端は fiber の余錐の標準局所比較への制限に等しい。
方針：相対 join の比較の一境界と、fiber の余錐の定値係数による表示を照合する。
規約：図式の表示の違いを避けて raw な射を比較する。
使われ方：fiber の余極限性を標準局所輸送の余錐へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：局所比較の終端は fiber の余錐を標準局所比較に沿って制限したもの。
方針：比較の一境界の定値係数を正規化し、fiber の余錐の持ち上げ表示と一致させる。
規約：充填性や余極限性は使わない。
使われ方：比較の両端の余極限性を結ぶ。 -/
lemma kanLocalRelativeJoinConeComparison_one {K C D : SSet.{u}} (δ : K ⟶ C)
    (H : relativeJoin (kanLeftCommaProjection δ) (𝟙 C) ⟶ D) (c : C _⦋0⦌) :
    prismEndpoint 1 (join (leftKanShape δ c) (Δ[0] : SSet.{u})) ≫
      kanLocalRelativeJoinConeComparison δ c ≫ H =
        ((kanRelativeJoinFiberCocone (kanLeftCommaProjection δ) c H).restrict
          (kanLeftKanShapeToCommaFiber δ c)).val := by
  have hA : joinInl (leftKanShape δ c) (Δ[0] : SSet.{u}) ≫
      (SSet.const (stdSimplex.obj₀Equiv.symm 0) ≫ SSet.yonedaEquiv.symm c) =
        (kanLeftKanShapeToCommaFiber δ c ≫ vertexFiberι (kanLeftCommaProjection δ) c) ≫
          kanLeftCommaProjection δ := by
    rw [SSet.yonedaEquiv_symm_zero, SSet.comp_const, SSet.comp_const,
      Category.assoc, vertexFiberι_comp, SSet.comp_const]
  rw [← Category.assoc]
  unfold kanLocalRelativeJoinConeComparison
  rw [kanRelativeJoinConeComparison_one _ _ _ _ _ _ hA]
  rw [kanRelativeJoinFiberCocone_restrict_val]
  have hb : (SSet.const (stdSimplex.obj₀Equiv.symm 0) :
      join (leftKanShape δ c) Δ[0] ⟶ Δ[0]) ≫ SSet.yonedaEquiv.symm c = SSet.const c := by
    rw [SSet.yonedaEquiv_symm_zero, SSet.comp_const]
  simp only [hb]

end SerrePositivity.InfinityCategories.F1B
