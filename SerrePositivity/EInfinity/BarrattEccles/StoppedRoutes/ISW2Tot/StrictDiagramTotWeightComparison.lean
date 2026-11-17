module
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.ProjectiveWeightComparison
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.BousfieldKanComparisonValues

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：strictなBE Totの指定一点重みとnative切断のBK重みを、一つの全重み比較で結ぶ。
方針：元のBKのcofibrancy、指定比較の各値の弱同値性、Kan係数へのHom不変性を合わせる。
規約：IS-W2 R03a。Jは元のAsSmall Δ、二重反対も保持し、係数ごとに比較射を選び直さない。
使われ方：元のTotの普遍重み付き錐を同じnative切断へ送る。
-/
@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory
open _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 元のstrict Totで全係数に共有する、一つの指定BK重み比較射。 -/
abbrev strictBETotWeightComparison :=
  _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkFramedWeightComparison (AsSmall.{u} SimplexCategory)

/-- 同じ一つの指定重み比較の制限は、元の全Kan係数図式でホモトピー同値。 -/
theorem strictBETotWeightComparison_homotopyEquivalence
    (H : ((AsSmall.{u} SimplexCategory)ᵒᵖᵒᵖ) ⥤ SSet.{u})
    (hH : ∀ i, SSet.KanComplex (H.obj i)) :
    IsSimplicialHomotopyEquivalence (weightedSectionsPre _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotWeightComparison H) :=
  _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.weightedSectionsPre_homotopyEquivalence_of_projective_cofibrant _ _ _ _
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bousfieldKanWeight_cofibrant _)
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight_cofibrant _)
    (_root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.bkFramedWeightComparison_weak _) H hH

/-- R03a：元のBK重みから指定一点重みへの一つの比較は、全Kan係数への制限のホモトピー同値。 -/
theorem exists_strictBETotWeightComparison :
    ∃ j : bousfieldKanWeight ((AsSmall.{u} SimplexCategory)ᵒᵖᵒᵖ) ⟶
        _root_.SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyWeight.framedLimitWeight (AsSmall.{u} SimplexCategory),
      ∀ (H : ((AsSmall.{u} SimplexCategory)ᵒᵖᵒᵖ) ⥤ SSet.{u}),
        (∀ i, SSet.KanComplex (H.obj i)) →
          IsSimplicialHomotopyEquivalence (weightedSectionsPre j H) :=
  ⟨_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotWeightComparison, _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotWeightComparison_homotopyEquivalence⟩

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
