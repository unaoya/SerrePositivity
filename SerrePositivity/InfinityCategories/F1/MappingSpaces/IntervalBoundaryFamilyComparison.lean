module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalFixedBoundaryFamily
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalTransportBoundaryFamily

/-!
概要：実際の区間族の全 lift 空間の可縮性は前合成同値で不変。
方針：区間データの自然性で族全体の比較の標的を同定する。
規約：内部の分類区間は固定しない。
使われ方：可縮な円柱族から元の区間族へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：実際の両端固定区間族の可縮性は全空間の前合成同値で保ち反映される。
方針：区間データの自然性と族全体の同値の可縮性不変性を合わせる。
規約：二つの境界包含の単射性だけを要求し比較射の単射性は要求しない。
使われ方：元の全空間と輸送円柱の実際の区間族の比較。 -/
lemma intervalBoundaryFamily_isContractibleKan_iff {M D K J : SSet.{u + 1}}
    (q : M ⟶ (Δ[1] : SSet.{u + 1})) (qD : D ⟶ (Δ[1] : SSet.{u + 1}))
    (c : D ⟶ M)
    (hc : IsPrecompositionEquivalence c)
    (jA : joinEndpointDiagram K J ⟶ M) (j : joinEndpointDiagram K J ⟶ D)
    (hj : j ≫ c = jA) (hq : c ≫ q = qD) [Mono j] [Mono jA]
    (hA₀ : (joinEndpointInl K J ≫ jA) ≫ q =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (hA₁ : (joinEndpointInr K J ≫ jA) ≫ q =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (hD₀ : (joinEndpointInl K J ≫ j) ≫ qD =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (hD₁ : (joinEndpointInr K J ≫ j) ≫ qD =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (rA : internalHom.PullbackObjObj jA pointedSpaceProjection)
    (rD : internalHom.PullbackObjObj j pointedSpaceProjection)
    {s t : SpaceInfinity.{u} _⦋0⦌}
    (g₀ : K ⟶ vertexFiber pointedSpaceProjection s)
    (g₁ : J ⟶ vertexFiber pointedSpaceProjection t) :
    IsContractibleKan (relativeBoundaryFamilySpace rA
      (intervalBoundaryFamilyData q jA hA₀ hA₁ rA g₀ g₁)) ↔
      IsContractibleKan (relativeBoundaryFamilySpace rD
        (intervalBoundaryFamilyData qD j hD₀ hD₁ rD g₀ g₁)) := by
  subst jA
  subst qD
  have he := (relativeBoundaryFamilyPre_isQCatEquivalence c hc j pointedSpaceProjection rA rD
    (intervalBoundaryFamilyData q (j ≫ c) hA₀ hA₁ rA g₀ g₁)).choose.isContractibleKan_iff
  rw [intervalBoundaryFamilyData_pre q c j hA₀ hA₁ hD₀ hD₁ rA rD g₀ g₁] at he
  exact he

end SerrePositivity.InfinityCategories
