module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CylinderFixedBoundaryFamily

/-!
概要：実際の境界固定区間データは全空間の前合成と可換。
方針：相対内部 Hom の二射影で境界の定値性と分類図式の前合成を確認する。
規約：底の区間の射も厳密に保持する。
使われ方：抽象的な族の比較を円柱と元の区間の実際のデータに同定する。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：全空間の前合成は実際の両端固定区間データの前合成と一致する。
方針：境界成分は不変、底の成分は内部 Hom の前合成の合成則を使う。
規約：各端点の可換性は厳密な等式として与える。
使われ方：実際の円柱族に対する比較の底のデータの同定。 -/
lemma intervalBoundaryFamilyData_pre {M D K J : SSet.{u + 1}}
    (q : M ⟶ (Δ[1] : SSet.{u + 1})) (c : D ⟶ M) (j : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDiagram K J ⟶ D)
    (hA₀ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl K J ≫ (j ≫ c)) ≫ q =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (hA₁ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr K J ≫ (j ≫ c)) ≫ q =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (hD₀ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInl K J ≫ j) ≫ (c ≫ q) =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (hD₁ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointInr K J ≫ j) ≫ (c ≫ q) =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (rA : internalHom.PullbackObjObj (j ≫ c) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection)
    (rD : internalHom.PullbackObjObj j _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection)
    {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌}
    (g₀ : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection s)
    (g₁ : J ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection t) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalBoundaryFamilyData q (j ≫ c) hA₀ hA₁ rA g₀ g₁ ≫
        _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryDataPre c j _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection rA rD =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalBoundaryFamilyData (c ≫ q) j hD₀ hD₁ rD g₀ g₁ := by
  apply rD.hom_ext
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryDataPre_fst]
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalBoundaryFamilyData]
    rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyData_fst, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyData_fst]
  · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryDataPre_snd]
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalBoundaryFamilyData]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyData_snd, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeBoundaryFamilyData_snd,
      Category.assoc, pre_map, NatTrans.comp_app]

/-- 概要：実際の輸送円柱比較は区間への射影を厳密に保持する。
方針：prism と終点の二つの pushout 包含で確認する。
規約：元の射影 p の fibration 性は要求しない。
使われ方：前合成した区間データを標準円柱データへ戻す。 -/
lemma intervalTransportCylinder_comparison_projection {E : SSet.{u}}
    (p : E ⟶ (Δ[1] : SSet.{u}))
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (H : Δ[1] ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ⟶ E)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ H = f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    (hp : H ≫ p = fst Δ[1] _) :
    pushout.desc H (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) h₁ ≫ p =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderIntervalProjection f := by
  apply pushout.hom_ext
  · rw [← Category.assoc, pushout.inl_desc, hp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderIntervalProjection_inl]
  · rw [← Category.assoc, pushout.inr_desc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderIntervalProjection_inr]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
