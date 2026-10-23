module

public import SerrePositivity.InfinityCategories.F1.Joins.ConeSectionsNativeComparison
public import SerrePositivity.InfinityCategories.F1.Joins.ConeTransformationEquivalence

/-!
概要：任意の小さい coherent 空間値図式の、元の全切断を頂点とする native 極限を証明する。
方針：元の全 Hom 比較を全切断への作用へ移し、同じ二比較の同値性を消去する。
規約：任意の小さい底。新たな極限存在や同値性の instance 仮定を要求しない。
使われ方：F1-4 の前層の小さい極限の各点存在を解消する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits
variable {B : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
local instance : KanComplex (simplicialSections (leftUnstraighteningProjection F)) :=
  simplicialSections_kanComplex (leftUnstraighteningProjection F)

/-- 任意の小さい図式で、元の全切断の錐の同じ native Hom 比較自体が同値。 -/
lemma coherentSectionsConeHomComparison_isQCatEquivalence (z : SpaceInfinity.{u} _⦋0⦌) :
    IsQCatEquivalence (fixedApexConeHomComparison (coherentDiagramSectionsCone F) z) := by
  have h := (coherentSectionsConeHomAction_isQCatEquivalence F z).ofFunctorIso
    (coneSectionsNativeComparisonIso (coherentDiagramSectionsCone F) z).symm
  have h' := (coherentConstantSourceMap_isQCatEquivalence F z).cancel_right h
  exact (coneTransformationMap_isQCatEquivalence F z).cancel_right h'

/-- 元の小さい全切断を頂点とする同じ native な錐は、任意の形状で極限錐。 -/
lemma coherentDiagramSectionsCone_isLimit : IsLimitCone (coherentDiagramSectionsCone F) := by
  apply (isLimitCone_iff_fixedApexConeHomComparison_homotopyEquivalence _).mpr
  intro z
  exact (coherentSectionsConeHomComparison_isQCatEquivalence F z).isSimplicialHomotopyEquivalence

/-- 任意の小さい coherent 空間値図式に、小さい全切断で表される極限が存在する。 -/
lemma hasLimit_coherentSpaceDiagram : HasLimit F :=
  ⟨coherentDiagramSectionsCone F, coherentDiagramSectionsCone_isLimit F⟩

end SerrePositivity.InfinityCategories
