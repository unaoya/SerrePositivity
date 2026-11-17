module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowEdgeComposition
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.LeftFibration
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.HomotopyOppositeEdges
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
/-!
概要：同じ twisted-arrow の左右射影の合成則をホモトピー圏の元の射で述べる。
方針：元の射の代表辺を取り、既存の反対ホモトピー圏の比較と三単体の計算を使う。
規約：結論は元の射自身についての等式で、新しい逆や成分を選ぶ結論ではない。
使われ方：元の corrected pairing の同じ指定関手同型の成分の合成則。
-/

@[expose] public section
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 元の twisted-arrow の射と両頂点の辺は、左右射影の同じ合成等式を満たす。 -/
lemma twistedArrowHom_composition {C : SSet.{u}} [Quasicategory C]
    {a b : (TwistedArrow C) _⦋0⦌}
    (f : HomotopyCategory.mk a ⟶ HomotopyCategory.mk b) :
    ((homotopyOppositeEquivalence C).functor.map
      ((SSet.mapHomotopyCategory (edgewiseLeft C)).map f)).unop ≫
        HomotopyCategory.homMk (twistedArrowVertexEdge a) ≫
          (SSet.mapHomotopyCategory (edgewiseRight C)).map f =
            HomotopyCategory.homMk (twistedArrowVertexEdge b) := by
  obtain ⟨s, hs⟩ := homotopyCategory_homMk_surjective a b f
  let e := SSet.Edge.ofTruncated s
  have he : HomotopyCategory.homMk e = f := hs
  rw [← he]
  simp only [SSet.mapHomotopyCategory_map_homMk]
  have hl := homotopyOppositeEquivalence_map_homMk (e.map (edgewiseLeft C)).toTruncated
  have h := congrArg Quiver.Hom.unop hl
  change ((homotopyOppositeEquivalence C).functor.map
    (HomotopyCategory.homMk (e.map (edgewiseLeft C)))).unop =
      HomotopyCategory.homMk (SSet.Edge.ofTruncated
        (SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edgeUnop
          (e.map (edgewiseLeft C)).toTruncated)) at h
  rw [h]
  exact twistedArrowEdge_composition e
end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

end
