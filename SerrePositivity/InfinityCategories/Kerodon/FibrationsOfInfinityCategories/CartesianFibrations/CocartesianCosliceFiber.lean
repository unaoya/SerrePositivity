module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianCosliceLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.InnerFiber

/-!
概要：基底の辺を固定した coslice の cocartesian な始対象。
方針：coslice の境界の相対充填を定値の基底の上で使う。
規約：fiber は基底の点の coslice の頂点上で取る。
使われ方：Kerodon §5.1.1（Tag 01T4）・§5.1.4（Tag 01U9） の輸送の普遍性。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：固定した基底の辺の持ち上げの圏で cocartesian な辺は始対象。
方針：最初の頂点を cocartesian な辺とする境界を基底の定値単体の上で充填する。
規約：quasicategory 性や p のファイブレーション性は不要。
使われ方：Kerodon §5.1.1（Tag 01T4） の cocartesian な辺の普遍性。 -/
lemma isInitialVertex_cocartesianCosliceFiber {E B : SSet.{u}}
    (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (a ≫ p)) _⦋0⦌)
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp a p) s) _⦋0⦌)
    (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianCosliceVertex a p t.val) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex t := by
  intro n f hf
  let f' := f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp a p) s
  have hw : f' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp a p =
      (boundary (n + 1)).ι ≫ SSet.const s := by
    dsimp [f']
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]
  have hfirst : SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ f') = t.val := by
    dsimp [f']
    rw [← Category.assoc, hf, SSet.yonedaEquiv_symm_comp, Equiv.apply_symm_apply]
    rfl
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianCosliceVertex a p
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ f')) := by
    rw [hfirst]
    exact ht
  obtain ⟨F, hF, hp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_coslice_boundary_lift_of_cocartesian_vertex a p n f'
    (SSet.const s) hw he
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp a p) s F hp, ?_⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp a p) s
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
  exact hF

/-- 概要：固定した基底の辺の cocartesian な持ち上げの選択は可縮な Kan 複体。
方針：cocartesian な coslice の射影の trivial Kan fibration 性を fiber に制限する。
規約：元・標的の quasicategory 性は不要。
使われ方：Kerodon §5.1.4（Tag 01U9） の輸送の選択の可縮性。 -/
lemma cocartesianCosliceFiber_isContractibleKan {E B : SSet.{u}}
    (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornFibration p]
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (a ≫ p)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianCosliceProjection a p) s) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan _ _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
