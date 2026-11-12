module

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.JoinEndpointPairMono
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ConeRestrictionCocartesianEdge

/-!
概要：錐の頂点と底の図式を同時に指定した先頭ホーンの延長。
方針：二端の余積から相対骨格の充填を適用し、両制限を回収する。
規約：安定性や有限極限を仮定しない。使われ方：一般安定性判定の全錐比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 先頭の辺が頂点で可逆なら、錐の両端を指定して外側ホーンを延長できる。 -/
lemma pointedCone_initialHorn_extend {K X : SSet.{u}} [Quasicategory X] (m : ℕ)
    (a₀ : (Δ[0] : SSet.{u}) ⟶ (ihom (Δ[m + 2] : SSet.{u})).obj X)
    (a : K ⟶ (ihom (Δ[m + 2] : SSet.{u})).obj X)
    (b : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K ⟶ (ihom (horn (m + 2) 0 : SSet.{u})).obj X)
    (h₀ : a₀ ≫ (pre (horn (m + 2) 0).ι).app X = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] K ≫ b)
    (h : a ≫ (pre (horn (m + 2) 0).ι).app X = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K ≫ b)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((uncurry b).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge m, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) K).app (Opposite.op ⦋0⦌)
          (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) 1)))) :
    ∃ F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K ⟶ (ihom (Δ[m + 2] : SSet.{u})).obj X,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] K ≫ F = a₀ ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K ≫ F = a ∧
        F ≫ (pre (horn (m + 2) 0).ι).app X = b := by
  let i := coprod.desc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) K) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) K)
  let : Mono i := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.joinEndpointPair_mono _ _
  have hw : coprod.desc a₀ a ≫ (pre (horn (m + 2) 0).ι).app X = i ≫ b := by
    apply coprod.hom_ext
    · simpa only [i, coprod.inl_desc_assoc] using h₀
    · simpa only [i, coprod.inr_desc_assoc] using h
  have ht (n : ℕ) (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) K) _⦋n⦌)
      (hs : s ∉ Set.range (i.app (Opposite.op ⦋n⦌))) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((uncurry b).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge m, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s) 1))) := by
    have hr : s ∉ Set.range ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) K).app (Opposite.op ⦋n⦌)) := by
      rintro ⟨t, rfl⟩
      apply hs
      refine ⟨(coprod.inr : K ⟶ (Δ[0] : SSet.{u}) ⨿ K).app (Opposite.op ⦋n⦌) t, ?_⟩
      exact ConcreteCategory.congr_hom
        (NatTrans.congr_app (coprod.inr_desc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[0] K) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[0] K)) _) t
    have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) K).app (Opposite.op ⦋0⦌)
          (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) := by
      unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex
      rw [SSet.yonedaEquiv_symm_app]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneSimplex_firstVertex_of_not_range s hr
    rw [hv]
    exact he
  obtain ⟨F, hF, hFb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.initialHornRestriction_lift_of_first_vertices i m
    (coprod.desc a₀ a) b hw ht
  refine ⟨F, ?_, ?_, hFb⟩
  · have hh := congrArg (fun q ↦ (coprod.inl : (Δ[0] : SSet.{u}) ⟶ Δ[0] ⨿ K) ≫ q) hF
    simpa only [i, coprod.inl_desc, coprod.inl_desc_assoc] using hh
  · have hh := congrArg (fun q ↦ (coprod.inr : K ⟶ (Δ[0] : SSet.{u}) ⨿ K) ≫ q) hF
    simpa only [i, coprod.inr_desc, coprod.inr_desc_assoc] using hh
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
