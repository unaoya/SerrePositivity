module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.CylinderFixedBoundaryFamily

/-!
概要：実際の境界固定区間データは全空間の前合成と可換。
方針：相対内部 Hom の二射影で境界の定値性と分類図式の前合成を確認する。
規約：底の区間の射も厳密に保持する。
使われ方：抽象的な族の比較を円柱と元の区間の実際のデータに同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：全空間の前合成は実際の両端固定区間データの前合成と一致する。
方針：境界成分は不変、底の成分は内部 Hom の前合成の合成則を使う。
規約：各端点の可換性は厳密な等式として与える。
使われ方：実際の円柱族に対する比較の底のデータの同定。 -/
lemma intervalBoundaryFamilyData_pre {M D K J : SSet.{u + 1}}
    (q : M ⟶ (Δ[1] : SSet.{u + 1})) (c : D ⟶ M) (j : joinEndpointDiagram K J ⟶ D)
    (hA₀ : (joinEndpointInl K J ≫ (j ≫ c)) ≫ q =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (hA₁ : (joinEndpointInr K J ≫ (j ≫ c)) ≫ q =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (hD₀ : (joinEndpointInl K J ≫ j) ≫ (c ≫ q) =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (hD₁ : (joinEndpointInr K J ≫ j) ≫ (c ≫ q) =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (rA : internalHom.PullbackObjObj (j ≫ c) pointedSpaceProjection)
    (rD : internalHom.PullbackObjObj j pointedSpaceProjection)
    {s t : SpaceInfinity.{u} _⦋0⦌}
    (g₀ : K ⟶ vertexFiber pointedSpaceProjection s)
    (g₁ : J ⟶ vertexFiber pointedSpaceProjection t) :
    intervalBoundaryFamilyData q (j ≫ c) hA₀ hA₁ rA g₀ g₁ ≫
        relativeBoundaryDataPre c j pointedSpaceProjection rA rD =
      intervalBoundaryFamilyData (c ≫ q) j hD₀ hD₁ rD g₀ g₁ := by
  apply rD.hom_ext
  · rw [Category.assoc, relativeBoundaryDataPre_fst]
    dsimp only [intervalBoundaryFamilyData]
    rw [relativeBoundaryFamilyData_fst, relativeBoundaryFamilyData_fst]
  · rw [Category.assoc, relativeBoundaryDataPre_snd]
    dsimp only [intervalBoundaryFamilyData]
    rw [← Category.assoc, relativeBoundaryFamilyData_snd, relativeBoundaryFamilyData_snd,
      Category.assoc, pre_map, NatTrans.comp_app]

/-- 概要：実際の輸送円柱比較は区間への射影を厳密に保持する。
方針：prism と終点の二つの pushout 包含で確認する。
規約：元の射影 p の fibration 性は要求しない。
使われ方：前合成した区間データを標準円柱データへ戻す。 -/
lemma intervalTransportCylinder_comparison_projection {E : SSet.{u}}
    (p : E ⟶ (Δ[1] : SSet.{u}))
    (f : vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ⟶
      vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (H : Δ[1] ⊗ vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ⟶ E)
    (h₁ : prismEndpoint 1 _ ≫ H = f ≫ vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (hp : H ≫ p = fst Δ[1] _) :
    pushout.desc H (vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) h₁ ≫ p =
      mappingCylinderIntervalProjection f := by
  apply pushout.hom_ext
  · rw [← Category.assoc, pushout.inl_desc, hp, mappingCylinderIntervalProjection_inl]
  · rw [← Category.assoc, pushout.inr_desc, vertexFiberι_comp,
      mappingCylinderIntervalProjection_inr]

end SerrePositivity.InfinityCategories
