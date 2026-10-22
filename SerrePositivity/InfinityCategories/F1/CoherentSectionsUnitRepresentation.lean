module

public import SerrePositivity.InfinityCategories.F1.CoherentSmallConstantSource
public import SerrePositivity.InfinityCategories.F1.IntervalMappingVertexEquivalence

/-!
概要：小さい全切断の恒等射を、定値図式から元の図式への変換として表す。
方針：定値始域比較の本質的全射性を使い、指定射への比較同型を保持する。
規約：元の図式と全切断の頂点を厳密に固定する。極限性は別工程。
使われ方：F1-4 の小さい全切断を頂点とする native 極限錐の実現。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {B : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})

/-- 頂点の対象表示だけを正規化した、元の全切断の恒等射。 -/
def coherentSpaceSectionsIdentity :
    (spaceInfinityObject (coherentSpaceSectionsVertex F)).obj ⟶
      (coherentSpaceSectionsObject F).obj :=
  eqToHom (coherentSpaceSectionsVertex_object F)

/-- 指定空間から全切断への射を表す変換と、その指定射への比較同型。 -/
def CoherentSectionsRepresentation (z : SpaceInfinity.{u} _⦋0⦌)
    (a : (spaceInfinityObject z).obj ⟶ (coherentSpaceSectionsObject F).obj) :=
  Σ t : (leftUnstraighteningTransformationSpace (SSet.const z) F) _⦋0⦌,
    VertexIso (X := (SSet.uliftFunctor.{u + 1, u}).obj
      ((ihom (spaceInfinityObject z).obj).obj (coherentSpaceSectionsObject F).obj))
      ((coherentSmallConstantSourceMap F z).app (Opposite.op ⦋0⦌) t)
      (ULift.up.{u + 1, u} (functorVertex a))

/-- 同じ全切断の恒等射を表す変換を、元の恒等射との比較同型とともに選ぶ。 -/
def coherentSectionsIdentityRepresentation :
    CoherentSectionsRepresentation F (coherentSpaceSectionsVertex F)
      (coherentSpaceSectionsIdentity F) :=
  Classical.choice <| by
    have h := coherentSmallConstantSourceMap_isQCatEquivalence F (coherentSpaceSectionsVertex F)
    obtain ⟨t, ⟨e⟩⟩ := h.choose.isEssentiallySurjective
      (ULift.up (functorVertex (coherentSpaceSectionsIdentity F)))
    exact ⟨⟨t, e⟩⟩

/-- 指定恒等射を表す変換を、定値頂点から元の図式への円柱に戻す。 -/
def coherentSectionsIdentityHomotopy :
    SSet.Homotopy (SSet.const (coherentSpaceSectionsVertex F)) F :=
  simplicialHomotopyOfFunctorEdge
    (intervalMappingEdgeOfVertex (coherentSectionsIdentityRepresentation F).1).toTruncated

end SerrePositivity.InfinityCategories
