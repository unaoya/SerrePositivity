module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.CosliceAlternatingFactorization
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.AlternatingStageExtension
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.RelativeAlternatingDiagram

/-!
概要：固定始域内で両成分の入力からの射を保持する全相対交互塔。
方針：同じ表示内の coslice 相対因子化を実際の一段延長へ渡す。
規約：底だけでなく固定始域内の全図式の整合を保持する。
使われ方：一般 accessible 引き戻しの小さい compact 成分対の生成。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：固定始域内の元の両表示を保持する全相対交互塔が存在する。
方針：同じ表示内の実際の相対因子化を全過去整合的な再帰へ渡す。
規約：余錐や延長の存在を追加入力として仮定しない。
使われ方：両成分入力からの全射を保持する長さ κ₀ の構成。 -/
lemma exists_relativeAlternatingTower_coslice_ind
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : IsCardinalChangeBound κ μ)
    {A S : SSet.{u}} [Quasicategory A] [Quasicategory S]
    (hS : IsKappaSmall μ S)
    (s₀ : (SSet.uliftFunctor.{u + 1, u}).obj S ⟶ Ind.IndInfinity μ A)
    (hs₀ : ∀ v, Compact.IsKappaCompact.{u, u + 1} μ (s₀.app (Opposite.op ⦋0⦌) v))
    {x : (Δ[0] : SSet.{u + 1}) ⟶ sliceUnder s₀}
    {I : Fin 2 → SSet.{u}} [∀ c, Quasicategory (I c)] [∀ c, IsKappaFiltered μ (I c)]
    {P : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (I c) ⟶ sliceOver x}
    (hP : ∀ c, ∀ v : (I c) _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ
      ((P c ≫ sliceOverProjection x ≫ sliceUnderProjection s₀).app (Opposite.op ⦋0⦌) (ULift.up v)))
    (hcol : ∀ c, IsColimitCone (mapJoinCocone (sliceUnderProjection s₀)
      (sliceDiagramCocone (P c))))
    : ∃ T : ∀ a, RelativeAlternatingClosedStage κ x I P a,
      ∀ a b, a < b → (T a).Restricts (T b) := by
  apply exists_relativeAlternatingTower_of_extension
  intro a s
  obtain ⟨t⟩ := exists_relativeAlternatingFactorization_coslice_ind
    h hS s₀ hs₀ hP hcol s (ofLex a).2
  exact exists_closedStage_of_relativeFactorization (ofLex a).1 (ofLex a).2 t

/-- 概要：固定始域内で両成分の全表示図式を保つ相対交互図式が存在する。
方針：実際の全相対塔を貼り合わせて元の成分表示への全制限を回収する。
規約：固定始域からの全高次成分も保持する。
使われ方：両成分の余極限比較と compact 成分対の生成。 -/
lemma exists_relativeAlternatingDiagram_coslice_ind
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : IsCardinalChangeBound κ μ)
    {A S : SSet.{u}} [Quasicategory A] [Quasicategory S]
    (hS : IsKappaSmall μ S)
    (s₀ : (SSet.uliftFunctor.{u + 1, u}).obj S ⟶ Ind.IndInfinity μ A)
    (hs₀ : ∀ v, Compact.IsKappaCompact.{u, u + 1} μ (s₀.app (Opposite.op ⦋0⦌) v))
    {x : (Δ[0] : SSet.{u + 1}) ⟶ sliceUnder s₀}
    {I : Fin 2 → SSet.{u}} [∀ c, Quasicategory (I c)] [∀ c, IsKappaFiltered μ (I c)]
    {P : ∀ c, (SSet.uliftFunctor.{u + 1, u}).obj (I c) ⟶ sliceOver x}
    (hP : ∀ c, ∀ v : (I c) _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ
      ((P c ≫ sliceOverProjection x ≫ sliceUnderProjection s₀).app (Opposite.op ⦋0⦌) (ULift.up v)))
    (hcol : ∀ c, IsColimitCone (mapJoinCocone (sliceUnderProjection s₀)
      (sliceDiagramCocone (P c))))
    : ∃ F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (AlternatingIndex κ)) ⟶ sliceOver x,
      ∃ J : ∀ c, nerve κ.ord.ToType ⟶ I c,
        ∀ c, (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (alternatingSection κ c)) ≫ F =
          (SSet.uliftFunctor.{u + 1, u}).map (J c) ≫ P c := by
  obtain ⟨T, hT⟩ := exists_relativeAlternatingTower_coslice_ind h hS s₀ hs₀ hP hcol
  obtain ⟨F, J, hc, _⟩ := exists_relativeAlternatingDiagram_of_tower T hT
  exact ⟨F, J, hc⟩

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
