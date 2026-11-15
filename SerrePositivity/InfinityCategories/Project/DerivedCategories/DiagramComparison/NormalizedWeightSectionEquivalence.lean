module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedWeightSectionMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductHomComparisonHomotopies
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.SimplicialHomotopyEquivalence
/-!
概要：元の正規化重みの指定切断比較は単体的ホモトピー同値。
方針：指定shuffleの逆と同じ二つのHomホモトピーを既存の単体同型で運ぶ。
規約：IS-W2 A09。別の同値を選ばず、指定射自身に逆を与える。
使われ方：HA 1.2.4、G10の豊穣Hom比較からnative極限性への接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CochainComplex
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] {J : Type u} [SmallCategory J]
variable (W : J ⥤ SSet.{u}) (Q : J ⥤ CochainComplex (ModuleCat A) ℤ)
variable (φ : simplicialRingCoefficient.{u} →+* A)
/-- 元の指定比較の実際の逆は同じshuffleによる指定逆射。 -/
theorem normalizedWeightSectionMap_equivalence :
    IsSimplicialHomotopyEquivalence (normalizedWeightSectionMap A W Q φ) := by
  refine ⟨normalizedWeightSectionReverse A W Q φ, ?_, ?_⟩
  · have h := functorHomotopyPrecomp
      (functorHomotopyPostcomp (freeProductHomReverse_homotopy A W φ Q)
        (freeTensorDiagramHomIso A Q W).hom) (freeTensorDiagramHomIso A Q W).inv
    simpa only [normalizedWeightSectionMap, normalizedWeightSectionReverse,
      Category.assoc, Iso.hom_inv_id_assoc, Category.id_comp, Iso.inv_hom_id,
      Category.comp_id] using (show Nonempty (SSet.Homotopy _ _) from ⟨h⟩)
  · have h := functorHomotopyPrecomp
      (functorHomotopyPostcomp (freeProductHomComparison_homotopy A W φ Q)
        (freeProductSectionsHomIso A W Q).hom) (freeProductSectionsHomIso A W Q).inv
    simpa only [normalizedWeightSectionMap, normalizedWeightSectionReverse,
      Category.assoc, Iso.hom_inv_id_assoc, Category.id_comp, Iso.inv_hom_id,
      Category.comp_id] using (show Nonempty (SSet.Homotopy _ _) from ⟨h⟩)
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
