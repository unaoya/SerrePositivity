module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKOriginalSections
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeCoherentCone
/-!
概要：元の正規化BK Homから元の図式の反転豊穣HomのBK endへの指定比較。
方針：指定反転・AW・添字移送の後に同じ実Γ Hom同型を合成する。
規約：IS-W2 A12。B02の指定錐の合成との等式とは別に、同じ射の同値性を示す。
使われ方：HA 1.2.4、G10のnative極限性への入力。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable {A : Type u} [CommRing A]
/-- 元の小図式のΓ Homを同じ反転豊穣Homへ運ぶ指定全自然同型。 -/
def normalizedBKReflectedHomDiagramIso (X : CosimplicialObject (Complex A)) (T : Complex A) :
    (((AsSmall.down : AsSmall.{u} SimplexCategory ⥤ SimplexCategory) ⋙
      (homDiagramFunctor T).obj X ⋙ truncatedDoldKanFunctor A) ⋙ SSet.opFunctor) ≅
    simplicialHomDiagram (liftedClosedDiagram X) (ForgetEnrichment.of (Complex A) T) ⋙
      SSet.opFunctor :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft ((AsSmall.down : AsSmall.{u} SimplexCategory ⥤ SimplexCategory) ⋙ X)
      (complexDoldKanHomIso A T).symm) SSet.opFunctor
/-- 元の反転BK Homから元の指定豊穣HomのBK endへの実際の比較射。 -/
def normalizedBKReflectedSectionsMap (X : CosimplicialObject (Complex A)) (T : Complex A) :
    ((truncatedDoldKanFunctor A).obj
      (normalizedBousfieldKanHom ((homDiagramFunctor T).obj X))).op ⟶
    bousfieldKanHolim (simplicialHomDiagram (liftedClosedDiagram X)
      (ForgetEnrichment.of (Complex A) T) ⋙ SSet.opFunctor) :=
  normalizedBKOriginalSectionsMap A ((homDiagramFunctor T).obj X) ≫
    (weightedSectionsFunctor (bousfieldKanWeight (AsSmall.{u} SimplexCategory))).map
      (normalizedBKReflectedHomDiagramIso X T).hom
open SSet.modelCategoryQuillen in
/-- 元の指定反転BK比較自身が単体的ホモトピー同値。 -/
theorem normalizedBKReflectedSectionsMap_equivalence (X : CosimplicialObject (Complex A))
    (T : Complex A) : IsSimplicialHomotopyEquivalence (normalizedBKReflectedSectionsMap X T) := by
  let Y := (homDiagramFunctor T).obj X
  have (i : AsSmall.{u} SimplexCategory) : SSet.KanComplex
      ((((AsSmall.down : AsSmall.{u} SimplexCategory ⥤ SimplexCategory) ⋙ Y ⋙
        truncatedDoldKanFunctor A) ⋙ SSet.opFunctor).obj i) := inferInstanceAs
          (SSet.KanComplex (((truncatedDoldKanFunctor A).obj
            (Y.obj ((AsSmall.down : AsSmall.{u} SimplexCategory ⥤ SimplexCategory).obj i))).op))
  have : SSet.KanComplex (bousfieldKanHolim
      (((AsSmall.down : AsSmall.{u} SimplexCategory ⥤ SimplexCategory) ⋙ Y ⋙
        truncatedDoldKanFunctor A) ⋙ SSet.opFunctor)) := bousfieldKanHolim_kanComplex _
  have : SSet.KanComplex
      ((weightedSectionsFunctor (bousfieldKanWeight (AsSmall.{u} SimplexCategory))).obj
        ((((AsSmall.down : AsSmall.{u} SimplexCategory ⥤ SimplexCategory) ⋙
          (homDiagramFunctor T).obj X ⋙ truncatedDoldKanFunctor A) ⋙ SSet.opFunctor))) :=
    (show SSet.KanComplex (bousfieldKanHolim
      (((AsSmall.down : AsSmall.{u} SimplexCategory ⥤ SimplexCategory) ⋙ Y ⋙
        truncatedDoldKanFunctor A) ⋙ SSet.opFunctor)) from inferInstance)
  let e := (weightedSectionsFunctor (bousfieldKanWeight (AsSmall.{u} SimplexCategory))).mapIso
    (normalizedBKReflectedHomDiagramIso X T)
  have : SSet.KanComplex
      ((weightedSectionsFunctor (bousfieldKanWeight (AsSmall.{u} SimplexCategory))).obj
        (simplicialHomDiagram (liftedClosedDiagram X)
          (ForgetEnrichment.of (Complex A) T) ⋙ SSet.opFunctor)) :=
    HomotopicalAlgebra.isFibrant_of_fibration e.inv
  exact ((normalizedBKOriginalSectionsMap_equivalence A Y).isQCatEquivalence.comp
    (qCatEquivalenceOfIso e).isQCatEquivalence).isSimplicialHomotopyEquivalence
end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
