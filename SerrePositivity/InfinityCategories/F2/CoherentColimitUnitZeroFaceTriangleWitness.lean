module

public import SerrePositivity.InfinityCategories.F2.FunctorTriangleRightEndpointNormalized
public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitZeroFaceLongWitness

/-!
概要：元の単位三単体の第零面の全持ち上げを、同じ実始域射の三角形証拠へ移す。
方針：結合子で全係数を保持し、元の全底・実第一辺の終点・実長辺の初期値を回収する。
規約：全選択と実延長を保持。使われ方：元の第零面への右辺の指定自然性の適用。
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
local notation "C" => leftUnstraightening F ⊗ K
local notation "p" => fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F
local notation "f" => coherentColimitUnitPointedFirstEdgeEndpoint B T k H he
local notation "D" => coherentColimitUnitPointedZeroFaceFamily B T k

/-- 元の全第零面を、同じ全係数・実第一辺の終点を持つ全三角形証拠として保持する。 -/
def coherentColimitUnitZeroFaceTriangleWitness : FunctorTrianglePointedWitness S p f where
  prism := (α_ Δ[2] (leftUnstraightening F) K).inv ≫
    coherentColimitUnitPointedZeroFaceLift B T k
  projection := by
    have hd : (D).diagram = fst (Δ[2] ⊗ (SSet.uliftFunctor.{u + 1, u}).obj B) K ≫
        functorSimplexDiagram S.diagram := by
      change _ ≫ functorSimplexDiagram _ = _
      rw [hS, Equiv.symm_apply_apply]
    rw [Category.assoc, coherentColimitUnitPointedZeroFaceLift_projection, hd]
    apply SSet.hom_ext
    intro n
    rfl
  initial := by
    have hv : simplexPrismVertex 2 0 C =
        prismEndpoint 0 C ≫ (stdSimplex.δ (1 : Fin 3) ▷ C) := by
      apply SSet.hom_ext
      intro n
      rfl
    rw [hv, Category.assoc]
    exact (coherentColimitUnitZeroFaceLongWitness B T k H he S hS false).initial.trans
      (coherentColimitUnitZeroFaceLong_initial B T k H he)

/-- 第零面の新しい証拠の実 prism は、元の同じ全族を結合子で表示したものに厳密に一致。 -/
lemma coherentColimitUnitZeroFaceTriangleWitness_prism :
    (coherentColimitUnitZeroFaceTriangleWitness B T k H he S hS).prism =
      Iso.inv (α_ Δ[2] (leftUnstraightening F) K) ≫
        coherentColimitUnitPointedZeroFaceLift B T k := rfl

end SerrePositivity.InfinityCategories.F2
