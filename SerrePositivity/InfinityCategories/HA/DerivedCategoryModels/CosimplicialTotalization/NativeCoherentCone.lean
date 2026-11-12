module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.EnrichedBousfieldKanCone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SmallBousfieldKanWeight
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ReflectedWeightedNativeCone

/-!
概要：元の積 Tot を頂点とする、strict 余単体図式の実 native coherent 錐。
方針：添字の宇宙を AsSmall で上げ、指定反転 BK 入力を既存の錐切断比較へ渡す。
規約：頂点を選び直さず、全高次単体を持つ join 錐を構成する。極限性は別に示す。
使われ方：HA 1.2.4、G10 の元の実現・Tot と native 錐の接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Opposite SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
variable {A : Type u} [CommRing A]

/-- 元の strict 余単体図式を、係数環の宇宙の添字圏で扱う。 -/
def liftedClosedDiagram (X : CosimplicialObject (Complex A)) :
    AsSmall.{u} SimplexCategory ⥤ ClosedCategory A (Complex A) :=
  AsSmall.down ⋙ X ⋙ SerrePositivity.EInfinity.ComplexLimits.complexToClosed A

/-- 同じ元の Tot を頂点とする、持ち上げた BK 重みから実反転 Hom への射。 -/
def liftedEnrichedBousfieldKanCone (X : CosimplicialObject (Complex A)) :
    bousfieldKanWeight (AsSmall.{u} SimplexCategory) ⟶
      simplicialHomDiagram (liftedClosedDiagram X)
        (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X)) ⋙ SSet.opFunctor :=
  smallBousfieldKanWeightDown SimplexCategory ≫
    Functor.whiskerLeft (AsSmall.down ⋙ (opOpEquivalence SimplexCategory).inverse)
      (enrichedBousfieldKanCone X)

/-- 指定 BK 代表から構成する、元の Tot を頂点とする実 join 錐。 -/
def nativeCoherentCone (X : CosimplicialObject (Complex A)) :
    JoinCone (strictCoherentDiagram (liftedClosedDiagram X)) :=
  reflectedWeightedNativeCone (liftedClosedDiagram X)
    (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
    (liftedEnrichedBousfieldKanCone X)

/-- native 錐の左端は元の積 Tot の頂点そのものである。 -/
theorem nativeCoherentCone_vertexMap (X : CosimplicialObject (Complex A)) :
    joinInl (Δ[0] : SSet.{u+1}) _ ≫ (nativeCoherentCone X).val =
      SSet.yonedaEquiv.symm (coherentNerveVertex
        (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))) :=
  reflectedWeightedNativeCone_vertexMap _ _ _

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
