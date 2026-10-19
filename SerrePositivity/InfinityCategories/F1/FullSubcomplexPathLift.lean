module

public import SerrePositivity.InfinityCategories.F1.InvertingFunctorIsoInvariance
public import SerrePositivity.InfinityCategories.Core.EquivalencePathVertices

/-!
概要：同型で不変な頂点条件を満たす全部分複体への可逆 path の復元。
方針：片端の条件から他端の条件を回収し、内部 Hom の全部分複体表示へ戻す。
規約：指定された path の族そのものを保持する。
使われ方：反転関手の制限の相対可逆 path の持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 可逆 path の二つの端点は、元のホモトピー圏で同型。 -/
def equivalencePathEndpointsVertexIso {X : SSet.{u}} (v : (equivalencePath X) _⦋0⦌) :
    VertexIso ((equivalencePathEndpoint X 0).app (Opposite.op ⦋0⦌) v)
      ((equivalencePathEndpoint X 1).app (Opposite.op ⦋0⦌) v) := by
  let e := edgeOfSimplex (intervalFunctorVertexEdge v.val)
  have hv : IsInvertibleEdge e := fullSubcomplexOnVertices_vertex v
  have he : equivalencePathVertex e hv = v := by
    apply Subtype.ext
    change functorVertex (SSet.yonedaEquiv.symm (intervalFunctorVertexEdge v.val)) = v.val
    obtain ⟨f, hf⟩ := (functorVertexEquiv (Δ[1] : SSet.{u}) X).surjective v.val
    rw [← hf]
    change functorVertex (SSet.yonedaEquiv.symm
      (intervalFunctorVertexEdge (functorVertex f))) = functorVertex f
    rw [intervalFunctorVertexEdge_functorVertex, Equiv.symm_apply_apply]
  rw [← he, equivalencePathVertex_zero, equivalencePathVertex_one]
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk e) := hv
  exact asIso (SSet.Truncated.HomotopyCategory.homMk e)

/-- 片端が条件を満たす可逆 path の族は、全ての区間頂点で条件を満たす。 -/
lemma equivalencePath_family_satisfies_of_endpoint {X K : SSet.{u}}
    (P : X _⦋0⦌ → Prop) (hP : ∀ {x y}, VertexIso x y → (P x ↔ P y))
    (H : K ⟶ equivalencePath X) (j : Fin 2)
    (hj : ∀ k : K _⦋0⦌, P ((H ≫ equivalencePathEndpoint X j).app (Opposite.op ⦋0⦌) k)) :
    ∀ k : K _⦋0⦌, FunctorVertexSatisfies (Δ[1] : SSet.{u}) X P
      ((H ≫ equivalencePathι X).app (Opposite.op ⦋0⦌) k) := by
  intro k t
  have hi := hP (equivalencePathEndpointsVertexIso (H.app (Opposite.op ⦋0⦌) k))
  obtain ⟨i, rfl⟩ := (stdSimplex.obj₀Equiv.symm).surjective t
  fin_cases j <;> fin_cases i
  · exact hj k
  · exact hi.mp (hj k)
  · exact hi.mpr (hj k)
  · exact hj k

/-- 同型不変な全部分複体に片端が入る可逆 path の族を、その部分複体へ戻す。 -/
def fullSubcomplexEquivalencePathLift {X K : SSet.{u}} [Quasicategory X]
    (P : X _⦋0⦌ → Prop) (hP : ∀ {x y}, VertexIso x y → (P x ↔ P y))
    (H : K ⟶ equivalencePath X) (j : Fin 2)
    (hj : ∀ k : K _⦋0⦌, P ((H ≫ equivalencePathEndpoint X j).app (Opposite.op ⦋0⦌) k)) :
    K ⟶ equivalencePath (fullSubcomplexOnVertices X P : SSet.{u}) := by
  let Q := fullSubcomplexLift (FunctorVertexSatisfies (Δ[1] : SSet.{u}) X P)
    (H ≫ equivalencePathι X) (equivalencePath_family_satisfies_of_endpoint P hP H j hj)
  let L := Q ≫ fullSubcomplexInternalHomBackward (Δ[1] : SSet.{u}) X P
  have hl : L ≫ (ihom (Δ[1] : SSet.{u})).map (fullSubcomplexOnVertices X P).ι =
      H ≫ equivalencePathι X := by
    rw [Category.assoc, fullSubcomplexInternalHomBackward_ι, fullSubcomplexLift_ι]
  refine fullSubcomplexLift IsEquivalencePathVertex L ?_
  intro k
  have he := congrArg (fun a : K ⟶ (ihom (Δ[1] : SSet.{u})).obj X ↦
    a.app (Opposite.op ⦋0⦌) k) hl
  have hh := fullSubcomplexOnVertices_vertex (H.app (Opposite.op ⦋0⦌) k)
  change (((ihom (Δ[1] : SSet.{u})).map (fullSubcomplexOnVertices X P).ι).app
    (Opposite.op ⦋0⦌) (L.app (Opposite.op ⦋0⦌) k)) = (H.app _ k).val at he
  have hm : IsEquivalencePathVertex
      (((ihom (Δ[1] : SSet.{u})).map (fullSubcomplexOnVertices X P).ι).app
        (Opposite.op ⦋0⦌) (L.app (Opposite.op ⦋0⦌) k)) := he.symm ▸ hh
  unfold IsEquivalencePathVertex at hm ⊢
  rw [intervalFunctorVertexEdge_map] at hm
  apply (isFullyFaithful_fullSubcomplexOnVertices_ι X P).reflects_isInvertibleEdge
    (edgeOfSimplex (intervalFunctorVertexEdge (L.app (Opposite.op ⦋0⦌) k)))
  exact (isInvertibleEdge_congr rfl).mpr hm

/-- 単射による可逆 path の像も単射。 -/
instance equivalencePathMap_mono {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] :
    Mono (equivalencePathMap f) := by
  have : Mono (equivalencePathι X) := by unfold equivalencePathι; infer_instance
  have : Mono ((ihom (Δ[1] : SSet.{u})).map f) := (ihom (Δ[1] : SSet.{u})).map_mono f
  exact mono_of_mono_fac (equivalencePathMap_ι f)

/-- 部分複体へ戻した可逆 path の族の像は、元の族そのもの。 -/
lemma fullSubcomplexEquivalencePathLift_map {X K : SSet.{u}} [Quasicategory X]
    (P : X _⦋0⦌ → Prop) (hP : ∀ {x y}, VertexIso x y → (P x ↔ P y))
    (H : K ⟶ equivalencePath X) (j : Fin 2)
    (hj : ∀ k : K _⦋0⦌, P ((H ≫ equivalencePathEndpoint X j).app (Opposite.op ⦋0⦌) k)) :
    fullSubcomplexEquivalencePathLift P hP H j hj ≫
        equivalencePathMap (fullSubcomplexOnVertices X P).ι = H := by
  have : Mono (equivalencePathι X) := by unfold equivalencePathι; infer_instance
  apply (cancel_mono (equivalencePathι X)).mp
  rw [Category.assoc, equivalencePathMap_ι, ← Category.assoc]
  dsimp only [fullSubcomplexEquivalencePathLift, equivalencePathι]
  rw [fullSubcomplexLift_ι, Category.assoc, fullSubcomplexInternalHomBackward_ι,
    fullSubcomplexLift_ι]

end SerrePositivity.InfinityCategories
