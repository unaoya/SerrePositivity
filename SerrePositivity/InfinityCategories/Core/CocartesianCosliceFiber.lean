module

public import SerrePositivity.InfinityCategories.Core.CocartesianCosliceLifting
public import SerrePositivity.InfinityCategories.Core.InnerFiber

/-!
概要：基底の辺を固定した coslice の cocartesian な始対象。
方針：coslice の境界の相対充填を定値の基底の上で使う。
規約：fiber は基底の点の coslice の頂点上で取る。
使われ方：Kerodon §5.1.1・§5.1.4 の輸送の普遍性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：固定した基底の辺の持ち上げの圏で cocartesian な辺は始対象。
方針：最初の頂点を cocartesian な辺とする境界を基底の定値単体の上で充填する。
規約：quasicategory 性や p のファイブレーション性は不要。
使われ方：Kerodon §5.1.1 の cocartesian な辺の普遍性。 -/
lemma isInitialVertex_cocartesianCosliceFiber {E B : SSet.{u}}
    (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B)
    (s : (sliceUnder (a ≫ p)) _⦋0⦌)
    (t : (vertexFiber (sliceUnderPostcomp a p) s) _⦋0⦌)
    (ht : IsCocartesianCosliceVertex a p t.val) : IsInitialVertex t := by
  intro n f hf
  let f' := f ≫ vertexFiberι (sliceUnderPostcomp a p) s
  have hw : f' ≫ sliceUnderPostcomp a p =
      (boundary (n + 1)).ι ≫ SSet.const s := by
    dsimp [f']
    rw [Category.assoc, vertexFiberι_comp, SSet.comp_const]
  have hfirst : SSet.yonedaEquiv (boundaryVertex n 0 ≫ f') = t.val := by
    dsimp [f']
    rw [← Category.assoc, hf, SSet.yonedaEquiv_symm_comp, Equiv.apply_symm_apply]
    rfl
  have he : IsCocartesianCosliceVertex a p
      (SSet.yonedaEquiv (boundaryVertex n 0 ≫ f')) := by
    rw [hfirst]
    exact ht
  obtain ⟨F, hF, hp⟩ := exists_coslice_boundary_lift_of_cocartesian_vertex a p n f'
    (SSet.const s) hw he
  refine ⟨vertexFiberLift (sliceUnderPostcomp a p) s F hp, ?_⟩
  apply vertexFiber_hom_ext (sliceUnderPostcomp a p) s
  rw [Category.assoc, vertexFiberLift_ι]
  exact hF

/-- 概要：固定した基底の辺の cocartesian な持ち上げの選択は可縮な Kan 複体。
方針：cocartesian な coslice の射影の trivial Kan fibration 性を fiber に制限する。
規約：元・標的の quasicategory 性は不要。
使われ方：Kerodon §5.1.4 の輸送の選択の可縮性。 -/
lemma cocartesianCosliceFiber_isContractibleKan {E B : SSet.{u}}
    (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B) [CocartesianHornFibration p]
    (s : (sliceUnder (a ≫ p)) _⦋0⦌) :
    IsContractibleKan (vertexFiber (cocartesianCosliceProjection a p) s) :=
  vertexFiber_isContractibleKan _ _

end SerrePositivity.InfinityCategories
