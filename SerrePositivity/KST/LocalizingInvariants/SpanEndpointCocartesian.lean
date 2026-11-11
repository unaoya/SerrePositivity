module

public import SerrePositivity.KST.LocalizingInvariants.SpanEndpointComplement
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianEdge

/-!
概要：共通始点で可逆な span の射は、二つの終点への制限に対して cocartesian。
方針：二変数を交換し、終点外の単体の最初の頂点で可逆な辺による相対充填を使う。
規約：値域は quasicategory。使われ方：固定第一終点の span 族の cocartesian 輸送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma hasCocartesianHornLifting_spanEndpointRestriction_of_apex
    {X : SSet.{u}} [Quasicategory X]
    {f g : ((ihom (horn 2 0 : SSet.{u})).obj X) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj ((ihom (horn 2 0 : SSet.{u})).obj X)) f g)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt spanApexVertex)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting ((pre spanEndpointInclusion).app X) e := by
  intro m σ β hσ hw
  let D := (horn 2 0 : SSet.{u})
  let K := (boundary 1 : SSet.{u})
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) K X β
  let b := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (horn (m + 2) 0 : SSet.{u}) D X σ
  have hsq : a ≫ (pre (horn (m + 2) 0).ι).app X = spanEndpointInclusion ≫ b := by
    have hh := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (horn (m + 2) 0 : SSet.{u}) K X) hw
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre] at hh
    exact hh.symm
  have ht (n : ℕ) (s : D _⦋n⦌)
      (hs : s ∉ Set.range (spanEndpointInclusion.app (Opposite.op ⦋n⦌))) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((uncurry b).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge m, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s) 1))) := by
    have hv := span_simplex_firstVertex_of_not_endpoints s hs
    have hedge : (uncurry b).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge m, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexFirstVertex s) 1) =
        (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt spanApexVertex))).edge := by
      rw [hv]
      dsimp [b, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv]
      rw [uncurry_curry]
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) spanApexVertex).app (Opposite.op ⦋1⦌)
        (σ.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge m)) = _
      rw [hσ]
      rfl
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr hedge).mpr he
  obtain ⟨F, hF₁, hF₂⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.initialHornRestriction_lift_of_first_vertices
    spanEndpointInclusion m a b hsq ht
  let G := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) D X).symm F
  have hG : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) D X G = F :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) D X).apply_symm_apply F
  refine ⟨G, ?_, ?_⟩
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (horn (m + 2) 0 : SSet.{u}) D X).injective
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre, hG]
    exact hF₂
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) K X).injective
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app, hG]
    exact hF₁

end SerrePositivity.KST.LocalizingInvariants
