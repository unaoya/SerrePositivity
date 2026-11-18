module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.SmallBKIndexSections
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.SmallBousfieldKanWeightIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedRestrictionIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKanHomotopyInvariance
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.OppositeKanHomotopy
/-!
概要：指定反転比較を元のΔの小添字と元のBK重みへ戻す。
方針：指定添字同型の後に元のsmallBousfieldKanWeightDownで前合成する。
規約：IS-W2 A12の証明分割。指定持ち下げを別の同値に取り替えない。
使われ方：HA 1.2.4、元の図式の反転Γ Homからnative錐への接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable (A : Type u) [CommRing A]
/-- 同じ指定添字移送と元の持ち下げが与える切断空間の同型。 -/
def normalizedBKOriginalSectionsIso (X : CosimplicialObject (Complex A)) :
    weightedSections (normalizedBKSmallWeight A)
      ((normalizedBKSmallDiagram A X ⋙ _root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A) ⋙ SSet.opFunctor) ≅
      bousfieldKanHolim
        (((AsSmall.down : AsSmall.{u} SimplexCategory ⥤ SimplexCategory) ⋙ X ⋙
          _root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A) ⋙ SSet.opFunctor) :=
  smallBKIndexSectionsIso (normalizedBKSmallWeight A)
      ((normalizedBKSmallDiagram A X ⋙ _root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A) ⋙ SSet.opFunctor) ≪≫
    weightedSectionsWeightIso (smallBousfieldKanWeightIso SimplexCategory)
      (((AsSmall.down : AsSmall.{u} SimplexCategory ⥤ SimplexCategory) ⋙ X ⋙
        _root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A) ⋙ SSet.opFunctor)
/-- 元のΔ添字と反転Γ係数を持つBK切断空間への指定比較。 -/
def normalizedBKOriginalSectionsMap (X : CosimplicialObject (Complex A)) :
    ((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).obj (normalizedBousfieldKanHom X)).op ⟶
      bousfieldKanHolim
        (((AsSmall.down : AsSmall.{u} SimplexCategory ⥤ SimplexCategory) ⋙ X ⋙
          _root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A) ⋙ SSet.opFunctor) :=
  normalizedBKSmallReflectedComparison A X ≫
    (smallBKIndexSectionsIso (normalizedBKSmallWeight A)
      ((normalizedBKSmallDiagram A X ⋙ _root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A) ⋙ SSet.opFunctor)).hom ≫
    weightedSectionsPre (smallBousfieldKanWeightDown SimplexCategory)
      (((AsSmall.down : AsSmall.{u} SimplexCategory ⥤ SimplexCategory) ⋙ X ⋙
        _root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A) ⋙ SSet.opFunctor)
/-- 元の指定射を反転end同型との合成に括り直す厳密な等式。 -/
theorem normalizedBKOriginalSectionsMap_factor (X : CosimplicialObject (Complex A)) :
    normalizedBKOriginalSectionsMap A X =
      SSet.opFunctor.map (normalizedBKReverseSpaceMap X ≫
        reflectedNormalizedBKSmallSectionsMap A X) ≫
      (SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsReflectedIso
        (normalizedBKSmallWeight A) (normalizedBKSmallDiagram A X ⋙ _root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A) ≪≫
          normalizedBKOriginalSectionsIso A X).hom := by
  simp only [normalizedBKOriginalSectionsMap, normalizedBKSmallReflectedComparison,
    normalizedBKOriginalSectionsIso, Iso.trans_hom, weightedSectionsWeightIso,
    smallBousfieldKanWeightIso_hom, Category.assoc]
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SSet.modelCategoryQuillen in
/-- 反転重み側の切断空間のKan性は元のBK endの指定同型から得る。 -/
instance reflectedNormalizedBKSmallSections_kan (X : CosimplicialObject (Complex A)) :
    SSet.KanComplex (weightedSections (reflectedNormalizedBKSmallWeight A)
      (normalizedBKSmallDiagram A X ⋙ _root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A)) := by
  have (i : AsSmall.{u} SimplexCategory) : SSet.KanComplex
      ((((AsSmall.down : AsSmall.{u} SimplexCategory ⥤ SimplexCategory) ⋙ X ⋙
        _root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A) ⋙ SSet.opFunctor).obj i) := inferInstanceAs
          (SSet.KanComplex (((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).obj (X.obj ((AsSmall.down : AsSmall.{u} SimplexCategory ⥤ SimplexCategory).obj i))).op))
  let S := weightedSections (reflectedNormalizedBKSmallWeight A)
    (normalizedBKSmallDiagram A X ⋙ _root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A)
  let e : S.op ≅ _ :=
    SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsReflectedIso
      (normalizedBKSmallWeight A) (normalizedBKSmallDiagram A X ⋙ _root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A) ≪≫
        normalizedBKOriginalSectionsIso A X

  have : SSet.KanComplex (bousfieldKanHolim
      (((AsSmall.down : AsSmall.{u} SimplexCategory ⥤ SimplexCategory) ⋙ X ⋙
        _root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A) ⋙ SSet.opFunctor)) := bousfieldKanHolim_kanComplex _
  let i := (SSet.opFunctorCompOpFunctorIso.app S).symm ≪≫ SSet.opFunctor.mapIso e
  exact HomotopicalAlgebra.isFibrant_of_fibration i.hom
/-- 元のΔ上の同じ指定比較自身が単体的ホモトピー同値。 -/
theorem normalizedBKOriginalSectionsMap_equivalence (X : CosimplicialObject (Complex A)) :
    IsSimplicialHomotopyEquivalence (normalizedBKOriginalSectionsMap A X) := by
  have (i : AsSmall.{u} SimplexCategory) : SSet.KanComplex
      ((((AsSmall.down : AsSmall.{u} SimplexCategory ⥤ SimplexCategory) ⋙ X ⋙
        _root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A) ⋙ SSet.opFunctor).obj i) := inferInstanceAs
          (SSet.KanComplex (((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).obj (X.obj ((AsSmall.down : AsSmall.{u} SimplexCategory ⥤ SimplexCategory).obj i))).op))
  have : SSet.KanComplex (weightedSections (normalizedBKSmallWeight A ⋙ SSet.opFunctor)
      (normalizedBKSmallDiagram A X ⋙ _root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A)) :=
    inferInstanceAs (SSet.KanComplex (weightedSections (reflectedNormalizedBKSmallWeight A)
      (normalizedBKSmallDiagram A X ⋙ _root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A)))
  have : SSet.KanComplex (bousfieldKanHolim
      (((AsSmall.down : AsSmall.{u} SimplexCategory ⥤ SimplexCategory) ⋙ X ⋙
        _root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A) ⋙ SSet.opFunctor)) := bousfieldKanHolim_kanComplex _
  have h := (normalizedBKReverseSpaceMap_equivalence X).comp
    (reflectedNormalizedBKSmallSectionsMap_equivalence A X)
  let e := SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedSectionsReflectedIso
    (normalizedBKSmallWeight A) (normalizedBKSmallDiagram A X ⋙ _root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A) ≪≫
      normalizedBKOriginalSectionsIso A X
  have he := (oppositeKanHomotopyEquivalence h).isQCatEquivalence.comp
    (qCatEquivalenceOfIso e).isQCatEquivalence
  rw [normalizedBKOriginalSectionsMap_factor]
  exact he.isSimplicialHomotopyEquivalence
end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
