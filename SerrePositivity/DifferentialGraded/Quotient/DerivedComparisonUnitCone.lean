module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonConeColimit
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonLayerGeneration
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonZeroModule

/-! # 商への代表加群比較の cone の局所生成

有限長比較 cone の厳密な余極限から、実際の比較射の cone へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 零段階から商全体への比較 cone の導来像は、S による有限因子分解性を持つ。 -/
lemma lengthInclusionCone_finiteCellFactorTarget (S : Set D) (h : localKFlat A D S) (z : D) :
    moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj
      (moduleCone A D (lengthModuleInclusion A D S z 0))) := by
  exact moduleSequentialColimit_finiteCellFactorTarget A D S
    (lengthComparisonConeDiagram A D S z)
    (fun n => lengthZeroToStageCone_finiteCellFactorTarget A D S h z n)
    (lengthComparisonConeCocone A D S z) (lengthComparisonConeCocone_isColimit A D S z)

/-- 始点の同型で結ばれる二つの射の cone は同型。 -/
def moduleConeSourceIso {M N T : ModuleCategory A D}
    (f : M ⟶ T) (g : N ⟶ T) (e : M ≅ N) (h : e.hom ≫ g = f) :
    moduleCone A D f ≅ moduleCone A D g :=
  (moduleConeFunctor A D).mapIso (X := Arrow.mk f) (Y := Arrow.mk g)
    (Arrow.isoMk' f g e (Iso.refl T) (by simpa using h))

/-- 元の代表加群を始点とする比較 cone と零段階を始点とする比較 cone の同型。 -/
def quotientRepresentableComparisonConeIso (S : Set D) (z : D) :
    moduleCone A D
        (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z) ≅
      moduleCone A D (lengthModuleInclusion A D S z 0) :=
  moduleConeSourceIso A D
    (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z)
    (lengthModuleInclusion A D S z 0) (lengthZeroModuleIso A D S z)
    (lengthZeroModuleMap_inclusion A D S z)

/-- 局所 K-flat 版の、商への実際の代表加群比較の cone の有限因子分解性。 -/
lemma quotientRepresentableComparisonCone_finiteCellFactorTarget
    (S : Set D) (h : localKFlat A D S) (z : D) :
    moduleFiniteCellFactorTarget A D S ((moduleToDerived A D).obj
      (moduleCone A D
        (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z))) :=
  (moduleFiniteCellFactorTarget A D S).prop_of_iso
    ((moduleToDerived A D).mapIso (quotientRepresentableComparisonConeIso A D S z)).symm
    (lengthInclusionCone_finiteCellFactorTarget A D S h z)

lemma quotientRepresentableComparison_trW (S : Set D) (h : localKFlat A D S) (z : D) :
    (moduleFiniteCellFactorTarget A D S).trW ((moduleToDerived A D).map
      (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z)) :=
  ((moduleFiniteCellFactorTarget A D S).trW_iff_of_distinguished
    (moduleDerivedConeTriangle A D
      (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z))
    (moduleDerivedConeTriangle_distinguished A D
      (representableRestrictionMap A D (QuotientObject D S) (inclusion A D S) z))).mpr
        (quotientRepresentableComparisonCone_finiteCellFactorTarget A D S h z)

end SerrePositivity.DifferentialGraded.DGQuotient
