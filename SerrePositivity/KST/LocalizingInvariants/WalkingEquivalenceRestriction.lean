module

public import SerrePositivity.KST.LocalizingInvariants.WalkingEquivalence
public import SerrePositivity.InfinityCategories.F1B.Fibrations.FinalHornFamily
public import SerrePositivity.InfinityCategories.Core.InternalHomFlipVertices

/-!
概要：自由な可逆区間の図式を、元の可逆辺の関手圏へ制限する。
方針：Kan な始域の辺は可逆なので、元の制限を可逆 path の全部分圏へ持ち上げる。
規約：標準区間への制限そのものを保持。使われ方：一般商の反転関手の普遍性。
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

def walkingEquivalenceRestriction (X : SSet.{u}) :
    (ihom walkingEquivalence).obj X ⟶ equivalencePath X :=
  fullSubcomplexLift IsEquivalencePathVertex ((pre walkingEquivalenceEdge).app X) (by
    intro v
    obtain ⟨F, rfl⟩ := (functorVertexEquiv walkingEquivalence X).surjective v
    change IsEquivalencePathVertex (functorVertex (walkingEquivalenceEdge ≫ F))
    rw [IsEquivalencePathVertex, intervalFunctorVertexEdge_functorVertex]
    rw [SSet.yonedaEquiv_comp]
    exact kanSource_map_invertible F (SSet.yonedaEquiv walkingEquivalenceEdge))

lemma walkingEquivalenceRestriction_ι (X : SSet.{u}) :
    walkingEquivalenceRestriction X ≫ equivalencePathι X =
      (pre walkingEquivalenceEdge).app X := fullSubcomplexLift_ι _ _ _

lemma equivalencePath_flip_invertible {B X : SSet.{u}} [Quasicategory X]
    (f : B ⟶ equivalencePath X) : IsInvertibleEdge (edgeOfSimplex (SSet.yonedaEquiv
      (internalHomFlipHomEquiv B (Δ[1] : SSet.{u}) X (f ≫ equivalencePathι X)))) := by
  apply SerrePositivity.InfinityCategories.functorSimplex_isInvertible_of_pointwise
  intro b
  have hb := fullSubcomplexOnVertices_vertex (f.app (Opposite.op ⦋0⦌) b)
  change IsEquivalencePathVertex (f.app (Opposite.op ⦋0⦌) b).val at hb
  have he := internalHomFlipHomEquiv_app_zero
    (internalHomFlipHomEquiv B (Δ[1] : SSet.{u}) X (f ≫ equivalencePathι X)) b
  change ((internalHomFlipHomEquiv B (Δ[1] : SSet.{u}) X).symm
    (internalHomFlipHomEquiv B (Δ[1] : SSet.{u}) X (f ≫ equivalencePathι X))).app
    (Opposite.op ⦋0⦌) b = _ at he
  rw [Equiv.symm_apply_apply] at he
  have hh := congrArg intervalFunctorVertexEdge he
  rw [intervalFunctorVertexEdge_functorVertex, SSet.yonedaEquiv_comp] at hh
  exact (isInvertibleEdge_congr hh).mp hb

end SerrePositivity.KST.LocalizingInvariants
