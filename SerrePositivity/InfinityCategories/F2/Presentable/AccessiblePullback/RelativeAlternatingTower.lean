module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.AlternatingStageExtension

/-!
概要：共通 κ₀ の全前置段を保持する相対交互塔が存在する。
方針：元の表示内の相対因子化を実際の閉前置段へ戻し、well-founded 選択を適用する。
規約：余錐や延長の存在を追加仮定として要求しない。
使われ方：二つの元の表示添字内での長さ κ₀ の交互構成。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：元の両表示を固定する整合した全相対交互塔が存在する。
方針：各位置で同じ成分表示の相対因子化を行い、全過去段への制限を保持する。
規約：長さ κ₀ の各極限位置でも全前置図式を使用する。
使われ方：小さい compact 成分対の生成と一般 accessible 引き戻し。 -/
lemma exists_relativeAlternatingTower
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : IsCardinalChangeBound κ μ)
    {A : SSet.{u}} [Quasicategory A]
    {x : (Δ[0] : SSet.{u + 1}) ⟶ Ind.IndInfinity μ A}
    {I : Fin 2 → SSet.{u}} [∀ c, Quasicategory (I c)] [∀ c, IsKappaFiltered μ (I c)]
    {P : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (I c) ⟶ sliceOver x}
    (hP : ∀ c, ∀ v : (I c) _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ
      ((P c ≫ sliceOverProjection x).app (Opposite.op ⦋0⦌) (ULift.up v)))
    (hcol : ∀ c, IsColimitCone (sliceDiagramCocone (P c))) :
    ∃ T : ∀ a : AlternatingIndex κ, RelativeAlternatingClosedStage κ x I P a,
      ∀ a b, a < b → (T a).Restricts (T b) := by
  apply exists_relativeAlternatingTower_of_extension
  intro a s
  obtain ⟨t⟩ := exists_relativeAlternatingFactorization h hP hcol s (ofLex a).2
  exact exists_closedStage_of_relativeFactorization (ofLex a).1 (ofLex a).2 t

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
