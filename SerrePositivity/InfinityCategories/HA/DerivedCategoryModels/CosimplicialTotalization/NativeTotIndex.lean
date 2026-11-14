module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeDGCone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.SmallDiagramShape

/-!
概要：同じAsSmall・ULiftの添字同型と、宇宙を揃えた元の余単体複体図式のnerveを固定する。
方針：既存nerveAsSmallIsoと二重ULiftの指定同型を合成する。
規約：IS-W2 C05のkappaとnerveMapの宇宙表記の具体化。元の全関手Xを保つ。
使われ方：HA 1.2.4、元のstrict図式への指定Tot錐の引き戻し。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory SSet SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped Simplicial
variable {A : Type u} [CommRing A]

/-- 元のAsSmall添字を戻し、同じ単体のULiftを一段にする指定同型。 -/
def nativeTotIndexIso :
    (SSet.uliftFunctor.{u+1,u}).obj (nerve (AsSmall.{u} SimplexCategory)) ≅
      (SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory) :=
  (SSet.uliftFunctor.{u+1,u}).mapIso (nerveAsSmallIso.{0,u} SimplexCategory).symm ≪≫
    smallDiagramShapeIso (nerve SimplexCategory)

/-- 元のstrict余単体複体図式のnerveを、対象とHomの実際の宇宙に揃えて読む。 -/
def strictCosimplicialComplexNerve (X : CosimplicialObject (Complex A)) :
    (SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory) ⟶ nerve (Complex A) :=
  (nerveAsSmallIso.{0,u+1} SimplexCategory).hom ≫
    resizedNerveMap (AsSmall.down ⋙ X)

/-- 指定添字同型は、元の同じ余単体次数の頂点を返す。 -/
theorem nativeTotIndexIso_vertex (n : SimplexCategory) :
    nativeTotIndexIso.{u}.hom.app (Opposite.op ⦋0⦌)
      (ULift.up (nerveVertex (AsSmall.up.obj n))) = ULift.up (nerveVertex n) := by
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
