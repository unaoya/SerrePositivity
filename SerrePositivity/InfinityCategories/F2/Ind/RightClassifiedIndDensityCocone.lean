module

public import SerrePositivity.InfinityCategories.F2.Ind.IndDensityCocone
public import SerrePositivity.InfinityCategories.F2.Ind.ClassifiedFilteredElements
public import SerrePositivity.InfinityCategories.F2.Ind.EquivalentCoconeRestriction
public import SerrePositivity.InfinityCategories.F1.UniverseQCatEquivalence

/-!
概要：元の κ-filtered right fibration 全空間を添字とする、同じ分類値の Indκ 内の密度余錐。
方針：元の復元同値で小さい密度余錐を制限し、元の射影を厳密に回収する。
規約：元の全空間・射影・分類値を保持。使われ方：strict 分類余極限と各段の密度比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  (p : RightFibrationObject C) [IsKappaFiltered κ p.val.left]

/-- 元の κ-filtered right fibration の同じ分類値は Indκ に属する。 -/
lemma rightClassified_isIndVertex :
    IsIndVertex κ C (functorVertex (rightStraighteningPresheafDiagram p)) := by
  apply isIndVertex_of_hasKappaFilteredElements
  exact (hasKappaFilteredElements_rightStraightening_iff κ p).mpr inferInstance

omit [IsKappaFiltered κ p.val.left] in
/-- 元の復元射による密度図式の制限は、元の射影と同じ Yoneda の合成。 -/
lemma rightClassifiedIndDensity_diagram :
    (SSet.uliftFunctor.{u + 1, u}).map (rightStraighteningSmallRecovery p) ≫
      indDensityDiagram κ (rightStraighteningPresheafDiagram p) =
        (SSet.uliftFunctor.{u + 1, u}).map p.val.hom ≫ indYoneda κ C := by
  rw [indDensityDiagram, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    rightStraighteningSmallRecovery_projection]

/-- 元の right fibration 全空間の同じ射影による Indκ 内の全密度余錐。 -/
def rightClassifiedIndDensityCocone :
    JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map p.val.hom ≫ indYoneda κ C) :=
  coherentCoconeOfDiagramEq (rightClassifiedIndDensity_diagram κ p)
    ((indDensityCocone κ (rightStraighteningPresheafDiagram p) (rightClassified_isIndVertex κ p)).restrict
      ((SSet.uliftFunctor.{u + 1, u}).map (rightStraighteningSmallRecovery p)))

/-- 同じ全密度余錐の射は、元の復元射による元の密度余錐の制限そのもの。 -/
lemma rightClassifiedIndDensityCocone_val :
    (rightClassifiedIndDensityCocone κ p).val =
      joinMap ((SSet.uliftFunctor.{u + 1, u}).map (rightStraighteningSmallRecovery p)) (𝟙 Δ[0]) ≫
        (indDensityCocone κ (rightStraighteningPresheafDiagram p) (rightClassified_isIndVertex κ p)).val :=
  coherentCoconeOfDiagramEq_val _ _

/-- 同じ密度余錐の頂点は、包含後に元の分類値を厳密に回収する。 -/
lemma rightClassifiedIndDensityCocone_vertex :
    (indInclusionPresheaf κ C).app (Opposite.op ⦋0⦌)
      (rightClassifiedIndDensityCocone κ p).vertex =
        functorVertex (rightStraighteningPresheafDiagram p) := by
  rw [rightClassifiedIndDensityCocone, coherentCoconeOfDiagramEq_vertex, JoinCocone.vertex_restrict]
  exact indDensityCocone_vertex κ _ _

/-- 元の全空間上の同じ全密度余錐は native な余極限。 -/
lemma rightClassifiedIndDensityCocone_isColimit :
    IsColimitCone (rightClassifiedIndDensityCocone κ p) := by
  apply (coherentCoconeOfDiagramEq_isColimit_iff _ _).mp
  exact (isColimitCone_iff_restrict_equivalentShape _
    (rightStraighteningSmallRecovery_isQCatEquivalence p).ulift _).mp
      (indDensityCocone_isColimit κ _ _)

end SerrePositivity.InfinityCategories.F2.Ind
