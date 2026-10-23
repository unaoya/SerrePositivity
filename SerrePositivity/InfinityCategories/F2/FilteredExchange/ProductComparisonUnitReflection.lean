module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ProductComparisonHomotopyDetection

/-!
概要：元の引き戻しからの有限二射の連結成分は、二つの全空間模型の成分で反映される。
方針：二つの fiber 内のホモトピーを検出し、元の輸送とともに Kan 模型へ送る。
規約：引き戻し自体の Kan 性を仮定しない。
使われ方：積比較の有限写像空間の単射性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：元の有限二射の二成分が同じなら、引き戻しの Kan 模型で同じ成分になる。
方針：同時の有限ホモトピー検出で得る三つのホモトピーを、単位への後合成で結ぶ。
規約：二成分は元の二射影そのもの。使われ方：積比較の単射性の元の射への還元。 -/
lemma totalKanProductComparison_unit_reflects_components {K E D B : SSet.{u}}
    [K.Finite] [Quasicategory B] [IsFilteredInfinity B]
    (p : E ⟶ B) [LeftFibration p] (q : D ⟶ B) [LeftFibration q]
    (a₀ a₁ : K ⟶ pullback p q)
    (h : SSet.π₀.mk (functorVertex (a₀ ≫ pullback.fst p q ≫ continuousKanReplacementUnit.app E)) =
      SSet.π₀.mk (functorVertex (a₁ ≫ pullback.fst p q ≫ continuousKanReplacementUnit.app E)))
    (g : SSet.π₀.mk (functorVertex (a₀ ≫ pullback.snd p q ≫ continuousKanReplacementUnit.app D)) =
      SSet.π₀.mk (functorVertex (a₁ ≫ pullback.snd p q ≫ continuousKanReplacementUnit.app D))) :
    SSet.π₀.mk (functorVertex (a₀ ≫ continuousKanReplacementUnit.app (pullback p q))) =
      SSet.π₀.mk (functorVertex (a₁ ≫ continuousKanReplacementUnit.app (pullback p q))) := by
  obtain ⟨H⟩ := (functorVertex_piZero_eq_iff_homotopy _ _).1 h
  obtain ⟨G⟩ := (functorVertex_piZero_eq_iff_homotopy _ _).1 g
  obtain ⟨c₀, c₁, ⟨H₀⟩, ⟨H₁⟩, ⟨Hc⟩⟩ :=
    totalKanProductComparison_finite_homotopy_detection p q a₀ a₁ H G
  have h₀ := (functorVertex_piZero_eq_iff_homotopy _ _).2
    ⟨functorHomotopyPostcomp H₀ (continuousKanReplacementUnit.app (pullback p q))⟩
  have h₁ := (functorVertex_piZero_eq_iff_homotopy _ _).2
    ⟨functorHomotopyPostcomp H₁ (continuousKanReplacementUnit.app (pullback p q))⟩
  have hc := (functorVertex_piZero_eq_iff_homotopy _ _).2
    ⟨functorHomotopyPostcomp Hc (continuousKanReplacementUnit.app (pullback p q))⟩
  exact h₀.trans (hc.trans h₁.symm)

end SerrePositivity.InfinityCategories.F2
