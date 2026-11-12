module
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-! # 引き戻し図式の全時刻整合的ホモトピー

概要：二射影上のホモトピーが全時刻で同じ底を持てば、引き戻し内で一つの比較を作る。
方針：全時間の射を引き戻しの普遍性で貼り、両端を二射影で検査する。
規約：底上の一致をホモトピー類へ弱めない。使われ方：slice 引き戻し内の有限図式の輸送。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits SSet

/-- 二射影上の全時刻整合的な比較は、引き戻し内の同じ二端点の実比較となる。 -/
def pullbackDiagramHomotopy {K E Y Q : SSet.{u}} (F : E ⟶ Q) (p : Y ⟶ Q)
    {f g : K ⟶ pullback F p}
    (A : SSet.Homotopy (f ≫ pullback.fst F p) (g ≫ pullback.fst F p))
    (B : SSet.Homotopy (f ≫ pullback.snd F p) (g ≫ pullback.snd F p))
    (h : A.h ≫ F = B.h ≫ p) : SSet.Homotopy f g where
  h := pullback.lift A.h B.h h
  h₀ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]
      exact A.h₀
    · rw [Category.assoc, pullback.lift_snd]
      exact B.h₀
  h₁ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]
      exact A.h₁
    · rw [Category.assoc, pullback.lift_snd]
      exact B.h₁
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

end SerrePositivity.InfinityCategories.Project.DerivedCategories
