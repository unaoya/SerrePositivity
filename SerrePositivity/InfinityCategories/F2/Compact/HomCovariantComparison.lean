module

public import SerrePositivity.InfinityCategories.F2.Compact.RepresentableCoslice
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.HomInfinityBifunctor
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.SourceInitial

/-!
概要：元の共同 Hom の共変制限を、定義に用いた元の全共変表現可能関手へ比較する。
方針：同じ始点固定 twisted arrow 射影と元の coslice を分類して合成する。
規約：全自然同型として比較し、各値の写像空間同値だけに弱めない。
使われ方：元の余極限図式から、全共変 Hom 関手の極限図式を構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
variable {C : SSet.{u}} [Quasicategory C]

/-- 元の共同 Hom の始点固定制限は、同じ元の始点固定全空間を分類する。 -/
def homInfinityCovariant_sourceIso (x : C _⦋0⦌) :
    FunctorIso (homInfinityCovariant x)
      (leftStraighteningInfinityDiagram (twistedArrowSourceProjection x)) := by
  have h : homInfinityCovariant x =
      (SSet.uliftFunctor.{u + 1, u}).map (twistedArrowSourceInclusion x) ≫
        twistedArrowHomInfinity C := by
    apply SSet.hom_ext
    intro n
    rfl
  rw [h]
  exact leftStraighteningInfinityDiagram_baseChangeIso
    (twistedArrowProjection C) (twistedArrowSourceInclusion x)

/-- 元の共同 Hom の共変制限と、元の全共変表現可能関手との全自然比較。 -/
def homInfinityCovariant_covariantIso (x : C _⦋0⦌) :
    FunctorIso (homInfinityCovariant x) (covariantRepresentableInfinity x) :=
  homInfinityCovariant_sourceIso x ≪≫
    (leftClassification_of_precompositionEquivalence
      (sliceUnderProjection (SSet.yonedaEquiv.symm x)) (twistedArrowSourceProjection x)
      (cosliceToTwistedArrowSource x) (cosliceToTwistedArrowSource_projection x)
      (cosliceToTwistedArrowSource_isPrecompositionEquivalence x)).symm ≪≫
    (covariantRepresentableInfinity_cosliceIso x).symm

end SerrePositivity.InfinityCategories.F2.Compact
