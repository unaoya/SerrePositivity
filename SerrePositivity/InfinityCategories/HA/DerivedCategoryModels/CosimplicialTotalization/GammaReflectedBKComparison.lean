module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKReflectedSections
/-!
概要：元の実豊穣Homから同じTotの反転BK endへの指定比較。
方針：実Hom同型、既存Hom–Tot比較、A12の指定射を合成する。
規約：IS-W2 B01とB03の証明分割。B02の豊穣合成との等式は別に示す。
使われ方：HA 1.2.4、元のnative錐の極限性への接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable {A : Type u} [CommRing A]
/-- 元の実豊穣Hom同型・同じHom–Tot比較・A12を合成した指定射。 -/
def gammaReflectedBKComparison (X : CosimplicialObject (Complex A))
    (x : ClosedCategory A (Complex A)) :
    (SimplicialCategory.sHom x
      (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))).op ⟶
    bousfieldKanHolim (simplicialHomDiagram (liftedClosedDiagram X) x ⋙ SSet.opFunctor) :=
  SSet.opFunctor.map ((doldKanSimplicialHomIso (R := A) x
      (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))).hom ≫
    normalizedBousfieldKanHomSpaceComparison (ForgetEnrichment.to (Complex A) x) X) ≫
      normalizedBKReflectedSectionsMap X (ForgetEnrichment.to (Complex A) x)
open SSet.modelCategoryQuillen in
/-- B02照合前の同じ指定合成射自身の単体的ホモトピー同値。 -/
theorem gammaReflectedBKComparison_equivalence (X : CosimplicialObject (Complex A))
    (x : ClosedCategory A (Complex A)) :
    IsSimplicialHomotopyEquivalence (gammaReflectedBKComparison X x) := by
  let T := ForgetEnrichment.to (Complex A) x
  let e := doldKanSimplicialHomIso (R := A) x
    (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
  have (i : AsSmall.{u} SimplexCategory) : SSet.KanComplex
      ((simplicialHomDiagram (liftedClosedDiagram X) x ⋙ SSet.opFunctor).obj i) := by
    change SSet.KanComplex ((SimplicialCategory.sHom x (ForgetEnrichment.of (Complex A)
      (X.obj ((AsSmall.down : AsSmall.{u} SimplexCategory ⥤ SimplexCategory).obj i)))).op)
    exact HomotopicalAlgebra.isFibrant_of_fibration (SSet.opFunctor.map
      (doldKanSimplicialHomIso (R := A) x (ForgetEnrichment.of (Complex A)
        (X.obj ((AsSmall.down : AsSmall.{u} SimplexCategory ⥤ SimplexCategory).obj i)))).hom)
  have : SSet.KanComplex
      (bousfieldKanHolim (simplicialHomDiagram (liftedClosedDiagram X) x ⋙ SSet.opFunctor)) :=
    bousfieldKanHolim_kanComplex _
  have : SSet.KanComplex (bousfieldKanHolim (simplicialHomDiagram (liftedClosedDiagram X)
      (ForgetEnrichment.of (Complex A) T) ⋙ SSet.opFunctor)) :=
    (show SSet.KanComplex (bousfieldKanHolim
      (simplicialHomDiagram (liftedClosedDiagram X) x ⋙ SSet.opFunctor)) from inferInstance)
  have h := (qCatEquivalenceOfIso (SSet.opFunctor.mapIso e)).isQCatEquivalence.comp
    (oppositeKanHomotopyEquivalence
      (normalizedBousfieldKanHomSpaceComparison_equivalence T X)).isQCatEquivalence
  have he := h.comp (normalizedBKReflectedSectionsMap_equivalence X T).isQCatEquivalence
  rw [gammaReflectedBKComparison, CategoryTheory.Functor.map_comp, Category.assoc]
  exact he.isSimplicialHomotopyEquivalence
end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
