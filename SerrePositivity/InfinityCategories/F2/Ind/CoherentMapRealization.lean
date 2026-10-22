module

public import SerrePositivity.InfinityCategories.F1.SmallCoherentMappingEquivalence
public import SerrePositivity.InfinityCategories.F1.IntervalMappingVertexEquivalence

/-!
概要：小さい unstraightening 間の実際の射を、同じ二図式間の coherent 変換で実現する。
方針：c1 の実際の写像空間比較の本質的全射性を使う。
規約：比較像と入力射の同型を相対写像空間内に保持し、存在だけに忘れない。
使われ方：密度の大域評価から自然変換を得る際の実現データ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {B : SSet.{u}}
  (H G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})

/-- 同じ小さい変換の頂点を、元の二図式間の自然変換として読む。 -/
def smallTransformationHomotopy (s : (smallLeftUnstraighteningTransformationSpace H G) _⦋0⦌) :
    SSet.Homotopy H G :=
  simplicialHomotopyOfFunctorEdge (intervalMappingEdgeOfVertex
    ((smallLeftUnstraighteningTransformationSpaceIso H G).hom.app (Opposite.op ⦋0⦌)
      (ULift.up s))).toTruncated

/-- 指定した実際の底上の射を実現する、c1 の変換と同じ相対像の比較。 -/
structure CoherentMapRealization
    (L : smallLeftUnstraightening H ⟶ smallLeftUnstraightening G)
    (hL : L ≫ smallLeftUnstraighteningProjection G = smallLeftUnstraighteningProjection H) where
  transformation : (smallLeftUnstraighteningTransformationSpace H G) _⦋0⦌
  imageIso : VertexIso
    ((smallLeftUnstraighteningMappingSpaceMap H G).app (Opposite.op ⦋0⦌) transformation)
    (relativeFunctorVertex (smallLeftUnstraighteningProjection G)
      (smallLeftUnstraighteningProjection H) L hL)

/-- 追加の同値性仮定なしに、元の射を同じ相対写像空間内で実現できる。 -/
lemma coherentMapRealization_nonempty
    (L : smallLeftUnstraightening H ⟶ smallLeftUnstraightening G)
    (hL : L ≫ smallLeftUnstraighteningProjection G = smallLeftUnstraighteningProjection H) :
    Nonempty (CoherentMapRealization H G L hL) := by
  let he := (smallLeftUnstraighteningMappingSpaceMap_isQCatEquivalence H G).choose
  obtain ⟨s, ⟨e⟩⟩ := he.isEssentiallySurjective
    (relativeFunctorVertex (smallLeftUnstraighteningProjection G)
      (smallLeftUnstraighteningProjection H) L hL)
  exact ⟨⟨s, e⟩⟩

end SerrePositivity.InfinityCategories.F2.Ind
