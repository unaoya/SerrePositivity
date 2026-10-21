module

public import SerrePositivity.KST.LocalizingInvariants.SpanEndpointComplement
public import SerrePositivity.InfinityCategories.Core.CocartesianEdge

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
    (he : IsInvertibleEdge (e.map ((truncation 2).map (evaluateFunctorAt spanApexVertex)))) :
    HasCocartesianHornLifting ((pre spanEndpointInclusion).app X) e := by
  intro m σ β hσ hw
  let D := (horn 2 0 : SSet.{u})
  let K := (boundary 1 : SSet.{u})
  let a := internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) K X β
  let b := internalHomFlipHomEquiv (horn (m + 2) 0 : SSet.{u}) D X σ
  have hsq : a ≫ (pre (horn (m + 2) 0).ι).app X = spanEndpointInclusion ≫ b := by
    have hh := congrArg (internalHomFlipHomEquiv (horn (m + 2) 0 : SSet.{u}) K X) hw
    rw [internalHomFlipHomEquiv_pre_app, internalHomFlipHomEquiv_pre] at hh
    exact hh.symm
  have ht (n : ℕ) (s : D _⦋n⦌)
      (hs : s ∉ Set.range (spanEndpointInclusion.app (Opposite.op ⦋n⦌))) :
      IsInvertibleEdge (edgeOfSimplex ((uncurry b).app (Opposite.op ⦋1⦌)
        (initialHornEdge m, PinchedHom.constant (simplexFirstVertex s) 1))) := by
    have hv := span_simplex_firstVertex_of_not_endpoints s hs
    have hedge : (uncurry b).app (Opposite.op ⦋1⦌)
        (initialHornEdge m, PinchedHom.constant (simplexFirstVertex s) 1) =
        (e.map ((truncation 2).map (evaluateFunctorAt spanApexVertex))).edge := by
      rw [hv]
      dsimp [b, internalHomFlipHomEquiv]
      rw [uncurry_curry]
      change (evaluateFunctorAt (Y := X) spanApexVertex).app (Opposite.op ⦋1⦌)
        (σ.app (Opposite.op ⦋1⦌) (initialHornEdge m)) = _
      rw [hσ]
      rfl
    exact (isInvertibleEdge_congr hedge).mpr he
  obtain ⟨F, hF₁, hF₂⟩ := initialHornRestriction_lift_of_first_vertices
    spanEndpointInclusion m a b hsq ht
  let G := (internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) D X).symm F
  have hG : internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) D X G = F :=
    (internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) D X).apply_symm_apply F
  refine ⟨G, ?_, ?_⟩
  · apply (internalHomFlipHomEquiv (horn (m + 2) 0 : SSet.{u}) D X).injective
    rw [internalHomFlipHomEquiv_pre, hG]
    exact hF₂
  · apply (internalHomFlipHomEquiv (Δ[m + 2] : SSet.{u}) K X).injective
    rw [internalHomFlipHomEquiv_pre_app, hG]
    exact hF₁

end SerrePositivity.KST.LocalizingInvariants
