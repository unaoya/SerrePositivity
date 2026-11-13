module

public import SerrePositivity.KST.LocalizingInvariants.SpanEndpointShape
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.RightJoinCoproduct
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinTensorPoint
public import SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryOne
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PointFunctorEvaluation

/-!
概要：元の span ホーンを、元の二端点の境界上の実錐形状と同定する。
方針：二辺の実 pushout と、区間境界の二点 coproduct の普遍性を使う。
規約：二端点と二つの実辺を厳密に保持する。
使われ方：固定端点 span と二終点上の全錐族の同じ比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 区間の元の境界は、順序を保持した二つの標準零単体の coproduct。 -/
def spanEndpointCoproductIso : (Δ[0] : SSet.{u}) ⨿ Δ[0] ≅ (boundary 1 : SSet.{u}) :=
  (coprodIsCoprod _ _).coconePointUniqueUpToIso
    SerrePositivity.HomotopyFunctionComplex.BoundaryOne.isColimit

lemma spanEndpointCoproductIso_left : (coprod.inl : (Δ[0] : SSet.{u}) ⟶ Δ[0] ⨿ Δ[0]) ≫
    spanEndpointCoproductIso.hom = boundary.ι (1 : Fin 2) :=
  (coprodIsCoprod _ _).comp_coconePointUniqueUpToIso_hom
    SerrePositivity.HomotopyFunctionComplex.BoundaryOne.isColimit
    (Discrete.mk WalkingPair.left)

lemma spanEndpointCoproductIso_right : (coprod.inr : (Δ[0] : SSet.{u}) ⟶ Δ[0] ⨿ Δ[0]) ≫
    spanEndpointCoproductIso.hom = boundary.ι (0 : Fin 2) :=
  (coprodIsCoprod _ _).comp_coconePointUniqueUpToIso_hom
    SerrePositivity.HomotopyFunctionComplex.BoundaryOne.isColimit
    (Discrete.mk WalkingPair.right)

lemma spanJoinHorn_isPushout : IsPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) Δ[0])
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) Δ[0])
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ horn₂₀.ι₀₁)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ horn₂₀.ι₀₂) := by
  apply horn₂₀.isPushout.of_iso (Iso.refl _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).symm (Iso.refl _)
  · rw [Iso.symm_hom, Iso.comp_inv_eq, Iso.refl_hom, Category.id_comp]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inl.symm
  · rw [Iso.symm_hom, Iso.comp_inv_eq, Iso.refl_hom, Category.id_comp]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inl.symm
  · simp only [Iso.refl_hom, Iso.symm_hom, Category.comp_id, Iso.inv_hom_id_assoc]
  · simp only [Iso.refl_hom, Iso.symm_hom, Category.comp_id, Iso.inv_hom_id_assoc]

/-- 共通の始点と二つの終点を持つ錐は、元の三頂点 span ホーン。 -/
def spanJoinHornIso : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) (Δ[0] ⨿ Δ[0]) ≅ (horn 2 0 : SSet.{u}) :=
  IsPushout.isoIsPushout _ _
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.join_right_coproduct_isPushout (Δ[0] : SSet.{u}) Δ[0] Δ[0]) spanJoinHorn_isPushout

lemma spanJoinHornIso_left :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (coprod.inl : (Δ[0] : SSet.{u}) ⟶ Δ[0] ⨿ Δ[0]) ≫
      spanJoinHornIso.hom = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ horn₂₀.ι₀₁ :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.join_right_coproduct_isPushout (Δ[0] : SSet.{u}) Δ[0] Δ[0]).inl_isoIsPushout_hom _ _ _

lemma spanJoinHornIso_right :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (coprod.inr : (Δ[0] : SSet.{u}) ⟶ Δ[0] ⨿ Δ[0]) ≫
      spanJoinHornIso.hom = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ horn₂₀.ι₀₂ :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.join_right_coproduct_isPushout (Δ[0] : SSet.{u}) Δ[0] Δ[0]).inr_isoIsPushout_hom _ _ _

/-- 区間の元の二端点上の錐形状と、元の span ホーンの厳密同型。 -/
def spanBoundaryConeIso : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) (boundary 1 : SSet.{u}) ≅
    (horn 2 0 : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso (Iso.refl _) spanEndpointCoproductIso.symm ≪≫ spanJoinHornIso

lemma spanBoundaryConeIso_left :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (boundary.ι (1 : Fin 2)) ≫
      spanBoundaryConeIso.hom = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ horn₂₀.ι₀₁ := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (boundary.ι (1 : Fin 2)) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) spanEndpointCoproductIso.inv ≫ spanJoinHornIso.hom) = _
  rw [← spanEndpointCoproductIso_left, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp,
    Category.id_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id, spanJoinHornIso_left]

lemma spanBoundaryConeIso_right :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (boundary.ι (0 : Fin 2)) ≫
      spanBoundaryConeIso.hom = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ horn₂₀.ι₀₂ := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (boundary.ι (0 : Fin 2)) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) spanEndpointCoproductIso.inv ≫ spanJoinHornIso.hom) = _
  rw [← spanEndpointCoproductIso_right, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp,
    Category.id_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id, spanJoinHornIso_right]

/-- 形状同型は元の二端点の境界包含をそのまま保持する。 -/
lemma spanBoundaryConeIso_endpoints :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) (boundary 1 : SSet.{u}) ≫ spanBoundaryConeIso.hom =
      spanEndpointInclusion.{u} := by
  apply (cancel_epi spanEndpointCoproductIso.hom).mp
  apply coprod.hom_ext
  · simp only [← Category.assoc, spanEndpointCoproductIso_left]
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap (𝟙 (Δ[0] : SSet.{u})) (boundary.ι (1 : Fin 2)),
      Category.assoc, spanBoundaryConeIso_left, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inr]
    apply (cancel_mono (horn 2 0).ι).mp
    simp only [Category.assoc, spanEndpointInclusion_ι]
    rw [← Category.assoc (boundary.ι (1 : Fin 2)), boundary.ι_ι]
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro s
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.stdSimplex_zero_eq_constant s]
    rfl
  · simp only [← Category.assoc, spanEndpointCoproductIso_right]
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap (𝟙 (Δ[0] : SSet.{u})) (boundary.ι (0 : Fin 2)),
      Category.assoc, spanBoundaryConeIso_right, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inr]
    apply (cancel_mono (horn 2 0).ι).mp
    simp only [Category.assoc, spanEndpointInclusion_ι]
    rw [← Category.assoc (boundary.ι (0 : Fin 2)), boundary.ι_ι]
    rfl

end SerrePositivity.KST.LocalizingInvariants
