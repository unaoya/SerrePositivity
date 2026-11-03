module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafPointwiseColimits
public import SerrePositivity.InfinityCategories.F1.Compact.UniverseColimits
public import SerrePositivity.InfinityCategories.Core.Compact.UniverseCoconePostcomposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafUniverseDiagram

/-!
概要：指定された前層の宇宙変更関手は、小さい coherent 余極限全余錐を保存する。
方針：同じ点での全評価の厳密な可換性を使い、空間の宇宙変更の保存性へ戻す。
規約：元の図式と指定余錐を保持し、底の quasicategory 性は仮定しない。
使われ方：P_Σ の延長の全 Hom 表示を、一段大きい前層圏で判定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
open F2.Compact

/-- 同じ前層の宇宙変更は、元の任意の小さい coherent 図式の指定余極限を保存する。 -/
lemma presheafUniverseDiagram_map_isColimit {I C : SSet.{u}} [Quasicategory I]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ PresheafInfinity C)
    (c : JoinCocone D) (hc : IsColimitCone c) :
    IsColimitCone (mapJoinCocone (presheafUniverseDiagram C)
      (JoinCocone.ulift.{u + 1, u + 2} c)) := by
  apply presheafInfinity_isColimit_of_evaluation _ _
  rintro ⟨y⟩
  change IsColimitCone (mapJoinCocone
    (presheafUniverseDiagram C ≫ presheafInfinityEvaluation (ULift.up y))
    (JoinCocone.ulift.{u + 1, u + 2} c))
  rw [presheafUniverseDiagram_evaluation, mapJoinCocone_universe_comp]
  exact spaceUniverseDiagram_map_isColimit (D ≫ presheafInfinityEvaluation y) _
    (presheafInfinity_evaluation_isColimit D c hc y)

end SerrePositivity.InfinityCategories.HomotopyLimits
