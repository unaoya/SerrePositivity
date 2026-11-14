module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKSmallHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedWeightSectionEquivalence
/-!
概要：元のBK HomのΓから同じ持ち上げ重み付き切断への指定比較。
方針：指定Hom同型のΓ像にA09の元のAW比較を合成する。
規約：IS-W2 A12の反転前の接続の証明分割。係数射は元の整数の指定射。
使われ方：HA 1.2.4、反転BK Holimへ戻す前の実比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CochainComplex
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable (A : Type u) [CommRing A]
/-- 同じ宇宙の指定整数係数環から元の係数環への標準射。 -/
def normalizedBKCoefficientMap : ULift.{u} ℤ →+* A :=
  (Int.castRingHom A).comp (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom
/-- 元のBK Homから同じ持ち上げBK重み付き切断への指定AW比較。 -/
def normalizedBKSmallSectionsMap (X : CosimplicialObject (Complex A)) :
    (truncatedDoldKanFunctor A).obj (normalizedBousfieldKanHom X) ⟶
      weightedSections (normalizedBKSmallWeight A)
        (normalizedBKSmallDiagram A X ⋙ truncatedDoldKanFunctor A) :=
  (truncatedDoldKanFunctor A).map (normalizedBKSmallHomIso A X).hom ≫
    normalizedWeightSectionMap A (normalizedBKSmallWeight A) (normalizedBKSmallDiagram A X)
      (normalizedBKCoefficientMap A)
/-- 同じ反転前の指定比較自身が単体的ホモトピー同値。 -/
theorem normalizedBKSmallSectionsMap_equivalence (X : CosimplicialObject (Complex A)) :
    IsSimplicialHomotopyEquivalence (normalizedBKSmallSectionsMap A X) := by
  let e := (truncatedDoldKanFunctor A).mapIso (normalizedBKSmallHomIso A X)
  let f := normalizedWeightSectionMap A (normalizedBKSmallWeight A) (normalizedBKSmallDiagram A X)
    (normalizedBKCoefficientMap A)
  change IsSimplicialHomotopyEquivalence (e.hom ≫ f)
  obtain ⟨r, ⟨hr⟩, ⟨hs⟩⟩ := normalizedWeightSectionMap_equivalence A
    (normalizedBKSmallWeight A) (normalizedBKSmallDiagram A X) (normalizedBKCoefficientMap A)
  refine ⟨r ≫ e.inv, ?_, ?_⟩
  · have h := functorHomotopyPrecomp (functorHomotopyPostcomp hr e.inv) e.hom
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp] using
      (show Nonempty (SSet.Homotopy _ _) from ⟨h⟩)
  · simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
      (show Nonempty (SSet.Homotopy _ _) from ⟨hs⟩)
end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
