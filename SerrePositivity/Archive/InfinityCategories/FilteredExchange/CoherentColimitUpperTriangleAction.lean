module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitNativeUnitTriangle
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitLowerAction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentNativeUnitValue
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorTriangleConstantTargetValue
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.UnstraighteningTriangleSecondVertexTransport

/-!
概要：上面の相対比較の値への像を、元の単位表現を持つ全空間比較へ照合する。
方針：同じ全上面の比較を元の値へ写し、第二辺の native 単位表示だけを揃える。
規約：元の全上面と単位表現を保持。使われ方：上下面比較の合成の値の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)
local notation "T" => coherentColimitNativeUnitTriangle B H
local notation "U" => coherentColimitNativeUnitFunctorTriangle B H
local notation "z" => coherentDiagramTotalVertex G
local notation "q" => Iso.hom (constantUnstraighteningRelativeIso
  (leftUnstraighteningProjection F) z)
local notation "m" => CategoryTheory.Functor.map (ihom (leftUnstraightening F))
  (QCatEquivalence.hom (pointedSpaceFiberValueEquivalence z))

/-- 元の変換の作用と同じ native 単位表現の作用を、元の値への合成射として読む。 -/
def coherentColimitUpperCompositeAction :=
  (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy H)).val ≫
    coherentNativeUnitValueAction G

/-- 元の上面と同じ native 単位表現の全空間比較を、元の値へ写す。 -/
def coherentColimitUpperTriangleActionIso :
    FunctorIso (coherentColimitLowerAction B H) (coherentColimitUpperCompositeAction B H) :=
  FunctorIso.postcomp (unstraighteningTriangleVertexIso F G (SSet.const z)
    (coherentVertexOfHomotopy H) (coherentNativeUnitRepresentation G).1 (T).diagonal
    (T).diagram (T).first (T).second (T).long)
    (constantUnstraighteningFiberProjection ((SSet.uliftFunctor.{u + 1, u}).obj B) z ≫
      (pointedSpaceFiberValueEquivalence z).hom)

/-- 上面の相対比較の像は、同じ native 単位表現を持つ元の上面作用比較と同じ値。 -/
lemma coherentColimitUpperRelativeComparison_map_heq_action :
    HEq (VertexIso.map (functorTriangleRelativeComparison U) (q ≫ m))
      (coherentColimitUpperTriangleActionIso B H) := by
  refine (functorTriangleRelativeComparison_map_constantTarget U).trans ?_
  exact unstraighteningTriangleVertexIso_postcomp_heq_second_eq F G (SSet.const z)
    (coherentVertexOfHomotopy H) (coherentVertexOfHomotopy (coherentNativeUnitHomotopy G))
    (coherentNativeUnitRepresentation G).1
    (coherentVertexOfHomotopy (coherentColimitNativeUnitDiagonal B H))
    (coherentTriangleOfFunctorTriangle U).diagram (coherentVertexOfHomotopy_of_vertex _)
    (coherentTriangleOfFunctorTriangle U).first (coherentTriangleOfFunctorTriangle U).second
    (T).second (coherentTriangleOfFunctorTriangle U).long _

end SerrePositivity.InfinityCategories.F2
