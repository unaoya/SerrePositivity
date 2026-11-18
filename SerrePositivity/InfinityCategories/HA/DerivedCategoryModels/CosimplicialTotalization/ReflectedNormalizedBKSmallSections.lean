module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedNormalizedBKSmallHom
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKSmallSections
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedSectionsOpposite
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedWeightSectionEquivalence
/-!
概要：反転正規化BK HomのΓから同じ持ち上げ重み付き切断への指定比較。
方針：指定Hom同型のΓ像にA09の元のAW比較を合成する。
規約：IS-W2 A12の反転重み側の接続の証明分割。係数射は元の整数の指定射。
使われ方：HA 1.2.4、反転BK Holimへ戻す前の実比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CochainComplex
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable (A : Type u) [CommRing A]
/-- 反転正規化BK Homから同じ持ち上げBK重み付き切断への指定AW比較。 -/
def reflectedNormalizedBKSmallSectionsMap (X : CosimplicialObject (Complex A)) :
    (_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).obj (reflectedNormalizedBKHom X) ⟶
      weightedSections (reflectedNormalizedBKSmallWeight A)
        (normalizedBKSmallDiagram A X ⋙ _root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A) :=
  (_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map (reflectedNormalizedBKSmallHomIso A X).hom ≫
    normalizedWeightSectionMap A (reflectedNormalizedBKSmallWeight A) (normalizedBKSmallDiagram A X)
      (normalizedBKCoefficientMap A)
/-- 同じ反転重み側の指定比較自身が単体的ホモトピー同値。 -/
theorem reflectedNormalizedBKSmallSectionsMap_equivalence (X : CosimplicialObject (Complex A)) :
    IsSimplicialHomotopyEquivalence (reflectedNormalizedBKSmallSectionsMap A X) := by
  let e := (_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).mapIso (reflectedNormalizedBKSmallHomIso A X)
  let f := normalizedWeightSectionMap A (reflectedNormalizedBKSmallWeight A) (normalizedBKSmallDiagram A X)
    (normalizedBKCoefficientMap A)
  change IsSimplicialHomotopyEquivalence (e.hom ≫ f)
  obtain ⟨r, ⟨hr⟩, ⟨hs⟩⟩ := normalizedWeightSectionMap_equivalence A
    (reflectedNormalizedBKSmallWeight A) (normalizedBKSmallDiagram A X) (normalizedBKCoefficientMap A)
  refine ⟨r ≫ e.inv, ?_, ?_⟩
  · have h := functorHomotopyPrecomp (functorHomotopyPostcomp hr e.inv) e.hom
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp] using
      (show Nonempty (SSet.Homotopy _ _) from ⟨h⟩)
  · simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
      (show Nonempty (SSet.Homotopy _ _) from ⟨hs⟩)
/-- Moore反転・同じAW比較・反転end同型を合成する実際の指定単体的射。 -/
def normalizedBKSmallReflectedComparison (X : CosimplicialObject (Complex A)) :
    ((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).obj (normalizedBousfieldKanHom X)).op ⟶
      weightedSections (normalizedBKSmallWeight A)
        ((normalizedBKSmallDiagram A X ⋙ _root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A) ⋙ SSet.opFunctor) :=
  SSet.opFunctor.map (normalizedBKReverseSpaceMap X ≫
    reflectedNormalizedBKSmallSectionsMap A X) ≫
      (SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsReflectedIso
        (normalizedBKSmallWeight A) (normalizedBKSmallDiagram A X ⋙ _root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A)).hom
end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
