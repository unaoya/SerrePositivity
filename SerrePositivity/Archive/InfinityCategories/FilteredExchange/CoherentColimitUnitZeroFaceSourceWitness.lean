module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitUnitZeroFaceLongComposition
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorHomotopySourceComponent

/-!
概要：元の第零面の実長辺を、全係数を保つ指定始域比較の証拠型へ移す。
方針：同じ普遍長辺の射影から底を同定し、元の初期値と終点を保持する。
規約：比較の値を保持。使われ方：既存の全族比較の成分への照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J Q₀ Q₁ Q₂ : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d) (k : Fin 3) (H : SSet.Homotopy F Q₀)
  (he : (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)) ≫
    SSet.yonedaEquiv.symm (coherentColimitUnitTriangleTetrahedron B T k) = curry H.h)
  {a : SSet.Homotopy Q₀ Q₁} {b : SSet.Homotopy Q₁ Q₂} {c : SSet.Homotopy Q₀ Q₂}
  (S : FunctorCompositionTriangle a b c)
  (hS : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ 0
    (coherentColimitUnitTriangleTetrahedron B T k) = SSet.yonedaEquiv S.diagram)
local notation "K" => coherentColimitUnitPointedTetrahedronChoice B T k
local notation "p" => fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F
local notation "f" => coherentColimitUnitPointedFirstEdgeEndpoint B T k H he
local notation "hf" => coherentColimitUnitPointedFirstEdgeEndpoint_projection B T k H he
local notation "Z" => coherentColimitUnitZeroFaceCanonicalLongWitness B T k H he S hS

include he hS in
/-- 同じ元の普遍長辺の射影から、指定長辺の全底の表示を揃える。 -/
lemma coherentColimitUnitZeroFaceLong_base_homotopy :
    (stdSimplex.δ (1 : Fin 3) ▷ (leftUnstraightening F ⊗ K)) ≫
      Iso.inv (α_ Δ[2] (leftUnstraightening F) K) ≫
      ((Δ[2] ◁ leftUnstraighteningProjection F) ▷ K) ≫
      PointedTransportPrismFamily.diagram (coherentColimitUnitPointedZeroFaceFamily B T k) =
      (Δ[1] ◁ p) ≫ functorSimplexDiagram (curry c.h) := by
  have hz := (Z).over.symm.trans (functorHomotopyPointedPrism_projection c f)
  rw [hf] at hz
  exact hz

/-- 実長辺の延長と終点を変えず、指定長辺の元の底・初期値の表示へ移す。 -/
def coherentColimitUnitZeroFaceSourceWitness (actual : Bool) :=
  let wSource := if actual then coherentColimitUnitZeroFaceLongWitness B T k H he S hS false
    else coherentColimitUnitZeroFaceCanonicalLongWitness B T k H he S hS
  wSource.transportData (coherentColimitUnitZeroFaceLong_base_homotopy B T k H he S hS)
    (coherentColimitUnitZeroFaceLong_initial B T k H he) rfl

/-- 普遍長辺は、元の同じ実始域を持つ普遍証拠そのもの。 -/
lemma coherentColimitUnitZeroFaceSourceWitness_canonical :
    coherentColimitUnitZeroFaceSourceWitness B T k H he S hS false =
      functorHomotopySourceCanonicalWitness c p f hf :=
  RelativeExtensionEndpointWitness.eq_of_extension_endpoint _ _ rfl rfl

/-- 元の長辺の指定始域比較を、元の同じ底・初期値で表示する。 -/
lemma coherentColimitUnitZeroFaceLongSourceIso_heq_homotopy :
    HEq (coherentColimitUnitZeroFaceLongSourceIso B T k H he S hS)
      (functorHomotopySourceEndpointIso c p f hf
        (coherentColimitUnitZeroFaceSourceWitness B T k H he S hS true)) := by
  let w₁ := coherentColimitUnitZeroFaceSourceWitness B T k H he S hS true
  have hh := RelativeExtensionEndpointWitness.iso_heq_of_dataEq (Z)
    (coherentColimitUnitZeroFaceLongWitness B T k H he S hS false)
    (functorHomotopySourceCanonicalWitness c p f hf) w₁
    (coherentColimitUnitZeroFaceLong_base_homotopy B T k H he S hS)
    (coherentColimitUnitZeroFaceLong_initial B T k H he) rfl rfl rfl rfl rfl
    (prismEndpoint_zero_leftAnodyne (leftUnstraightening F ⊗ K))
    (coherentColimitUnitZeroFaceLong_base_initial B T k H he S hS) w₁.initial_base
    (coherentColimitUnitZeroFaceLong_base_endpoint B T k H he S hS) w₁.endpoint_base
  exact hh

end SerrePositivity.InfinityCategories.F2
