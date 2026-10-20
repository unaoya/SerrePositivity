module

public import SerrePositivity.InfinityCategories.F2.TransportTrianglePrismWitness
public import SerrePositivity.InfinityCategories.F1.UnstraighteningFamilyWitnessRestriction

/-!
概要：標準 unstraightening の二辺の全三角形から長辺の証拠を直接得る。
方針：同じ保持した prism を標準表現の座標へ戻す。
規約：証拠の存在から再選択しない。使われ方：指定された合成比較同型。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：保持した元の全三角形の長辺を標準 unstraightening の証拠にする。
方針：標準表現の比較が恒等であることを使い端点表示だけを揃える。
規約：元の長辺 prism を保持。使われ方：存在だけからの同型の再選択を除く。 -/
def unstraighteningFamilyTriangleWitnessOfPrism {B K : SSet.{u + 1}}
    (F G J : B ⟶ SpaceInfinity.{u})
    {a : K ⟶ leftUnstraighteningTransformationSpace F G}
    {b : K ⟶ leftUnstraighteningTransformationSpace G J}
    {c : K ⟶ leftUnstraighteningTransformationSpace F J}
    {f : leftUnstraightening F ⊗ K ⟶ leftUnstraightening G}
    {g : leftUnstraightening G ⊗ K ⟶ leftUnstraightening J}
    (w : UnstraighteningFamilyWitness F G a f)
    (v : UnstraighteningFamilyWitness G J b g)
    (H : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ SpaceInfinity.{u})
    (L : TransportTrianglePrism w.toRepresentationWitness v.toRepresentationWitness H)
    (h₀₂ : (stdSimplex.δ (1 : Fin 3) ▷ (B ⊗ K)) ≫ H =
      coherentTransformationFamilyDiagram c) :
    UnstraighteningFamilyWitness F J c
      (lift f (snd (leftUnstraightening F) K) ≫ g) := by
  let W := L.longWitness h₀₂
  refine ⟨W.prism, ?_, ?_, W.projection⟩
  · simpa only [unstraighteningTransportRepresentation, LeftTransportRepresentation.pointedMap,
      Category.id_comp] using W.source
  · simpa only [unstraighteningTransportRepresentation, LeftTransportRepresentation.pointedMap,
      Category.id_comp] using W.target

end SerrePositivity.InfinityCategories.F2
