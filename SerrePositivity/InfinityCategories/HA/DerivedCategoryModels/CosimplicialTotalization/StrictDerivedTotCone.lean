module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeDerivedDiagramEq
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SpecifiedConeReindex

/-!
概要：元のstrict余単体図式そのものの上に、同じ全join射の導来Tot錐を置く。
方針：指定添字同型の逆に制限し、C05の厳密等式で底図式だけを移す。
規約：IS-W2 C06・C07。頂点・脚・全高次単体を置き換えない。
使われ方：HA 1.2.4、元の複体の実積Totとnative極限の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory SSet SerrePositivity.DifferentialGraded
open _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped Simplicial
variable {A : Type u} [CommRing A]

/-- 同じ添字同型の逆で元のstrict図式へ戻す底図式の等式。 -/
theorem nativeDerivedDiagram_reindex (X : CosimplicialObject (Complex A)) :
    nativeTotIndexIso.inv ≫ nativeDerivedDiagram X =
      strictCosimplicialComplexNerve X ≫ _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A := by
  rw [nativeDerivedDiagram_eq, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- 元のstrict図式の同じ指定Tot錐。 -/
def strictDerivedTotCone (X : CosimplicialObject (Complex A)) :
    JoinCone (strictCosimplicialComplexNerve X ≫ _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A) :=
  joinConeOfDiagramEq (nativeDerivedDiagram_reindex X)
    (restrictJoinCone (nativeDerivedCone X) nativeTotIndexIso.inv)

/-- 元のstrict図式の同じ指定Tot錐はnative極限錐。 -/
theorem strictDerivedTotCone_isLimit (X : CosimplicialObject (Complex A)) :
    IsLimitCone (strictDerivedTotCone X) :=
  joinConeOfDiagramEq_isLimit _ _
    (restrictJoinCone_isLimit_of_isIso _ _ (nativeDerivedCone_isLimit X))

/-- 添字同型で戻すと、元の全join射そのものになる。 -/
theorem strictDerivedTotCone_pullback (X : CosimplicialObject (Complex A)) :
    joinMap (𝟙 (Δ[0] : SSet.{u+1})) nativeTotIndexIso.hom ≫
      (strictDerivedTotCone X).val = (nativeDerivedCone X).val := by
  rw [strictDerivedTotCone, joinConeOfDiagramEq_val]
  change joinMap _ nativeTotIndexIso.hom ≫
    (joinMap _ nativeTotIndexIso.inv ≫ (nativeDerivedCone X).val) = _
  rw [← Category.assoc, ← joinMap_comp, Category.id_comp, Iso.hom_inv_id, joinMap_id,
    Category.id_comp]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
