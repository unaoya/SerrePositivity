module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitLowerCompositeValue

/-!
概要：下面の区間族比較の両端を、元の三辺の相対頂点と厳密に照合する。
方針：元の単位と指定区間の全族の等式を相対合成の頂点式に適用する。
規約：元の両端を保持。使われ方：指定値の一致を元の値への後合成で写す。
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
local notation "B'" => CategoryTheory.Functor.obj SSet.uliftFunctor B
local notation "z" => coherentDiagramTotalVertex G
local notation "v" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "u₀" => coconeTransformationHomotopy (coherentDiagramTotalCocone F)
local notation "c" => coherentColimitIntervalConstantHomotopy B H
local notation "d" => coherentColimitNativeUnitDiagonal B H

/-- 下面の指定族比較の始点は、同じ対角の元の相対頂点。 -/
lemma coherentColimitLowerComposite_source_vertex :
    (((SSet.const (coherentVertexOfHomotopy d) : (Δ[0] : SSet.{u + 1}) ⟶ _) ≫
      leftUnstraighteningMappingSpaceMap F (SSet.const z)).app (Opposite.op ⦋0⦌) v) =
      relativeFunctorVertex (leftUnstraighteningProjection (SSet.const z : B' ⟶ _))
        (leftUnstraighteningProjection F)
        (leftUnstraighteningMappingVertexMap F (SSet.const z) (coherentVertexOfHomotopy d)).val
        (leftUnstraighteningMappingVertexMap F (SSet.const z)
          (coherentVertexOfHomotopy d)).property :=
  unstraighteningMappingConst_vertex F (SSet.const z) _ v

/-- 下面の指定区間族の合成頂点は、同じ元の単位作用と第二辺の作用の相対合成。 -/
lemma coherentColimitLowerComposite_target_vertex :
    (coconeIntervalRelativeComposite (coherentDiagramTotalCocone F)
      (SSet.yonedaEquiv.symm (coherentColimitIntervalVertex B H))).app (Opposite.op ⦋0⦌) v =
      relativeFunctorVertex (leftUnstraighteningProjection (SSet.const z : B' ⟶ _))
        (leftUnstraighteningProjection F)
        ((leftUnstraighteningMappingVertexMap F
          (SSet.const (coherentDiagramTotalCocone F).vertex) (coherentVertexOfHomotopy u₀)).val ≫
          (leftUnstraighteningMappingVertexMap
            (SSet.const (coherentDiagramTotalCocone F).vertex) (SSet.const z)
              (coherentVertexOfHomotopy c)).val)
        (by rw [Category.assoc,
          (leftUnstraighteningMappingVertexMap
            (SSet.const (coherentDiagramTotalCocone F).vertex) (SSet.const z)
              (coherentVertexOfHomotopy c)).property,
          (leftUnstraighteningMappingVertexMap F
            (SSet.const (coherentDiagramTotalCocone F).vertex)
              (coherentVertexOfHomotopy u₀)).property]) := by
  have hb := coherentColimitIntervalVertex_constant B H
  unfold coconeIntervalRelativeComposite constantUnstraighteningComposite
  simp only [SSet.yonedaEquiv_symm_zero] at hb ⊢
  rw [hb, ← coherentVertexOfHomotopy_cocone]
  exact unstraighteningMappingConstComposite_vertex _ _ _ _ _ v

end SerrePositivity.InfinityCategories.F2
