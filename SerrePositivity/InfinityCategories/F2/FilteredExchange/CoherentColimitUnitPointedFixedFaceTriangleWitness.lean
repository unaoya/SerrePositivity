module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTriangleRightEndpointNormalized
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitPointedFixedFaceLongWitness

/-!
概要：元の単位三単体の固定始点の二面の全持ち上げを、同じ全係数の三角形証拠へ移す。
方針：元の全底と同じ初期値を、結合子と元の実長辺の初期式で厳密に回収する。
規約：全選択と実延長を保持。使われ方：固定面への右辺の指定自然性の適用。
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
  {F G J Q₁ Q₂ : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d) (k : Fin 3) (j : Fin 4) (hj : j ≠ 0)
  {a : SSet.Homotopy F Q₁} {b : SSet.Homotopy Q₁ Q₂} {c : SSet.Homotopy F Q₂}
  (S : FunctorCompositionTriangle a b c)
  (hS : ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}).δ j
    (coherentColimitUnitTriangleTetrahedron B T k) = SSet.yonedaEquiv S.diagram)
local notation "K" => coherentColimitUnitPointedTetrahedronChoice B T k
local notation "C" => leftUnstraightening F ⊗ K
local notation "p" => fst (leftUnstraightening F) K ≫ leftUnstraighteningProjection F

/-- 元の全固定面を、同じ全係数・元の全空間射影を持つ全三角形証拠として保持する。 -/
def coherentColimitUnitPointedFixedFaceTriangleWitness :
    FunctorTrianglePointedWitness S p (fst (leftUnstraightening F) K) where
  prism := (α_ Δ[2] (leftUnstraightening F) K).inv ≫
    coherentColimitUnitPointedFixedFaceLift B T k j
  projection := by
    rw [Category.assoc, coherentColimitUnitPointedFixedFaceLift_projection B T k j hj S hS]
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
    exact (coherentColimitUnitPointedFixedFaceLongWitness B T k j hj S hS false).initial.trans
      (coherentColimitUnitPointedFixedFaceLong_initial B T k j hj S hS)

/-- 固定面の新しい証拠の実 prism は、元の同じ全族を結合子で表示したものに厳密に一致。 -/
lemma coherentColimitUnitPointedFixedFaceTriangleWitness_prism :
    (coherentColimitUnitPointedFixedFaceTriangleWitness B T k j hj S hS).prism =
      Iso.inv (α_ Δ[2] (leftUnstraightening F) K) ≫
        coherentColimitUnitPointedFixedFaceLift B T k j := rfl

end SerrePositivity.InfinityCategories.F2
