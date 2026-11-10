module

public import SerrePositivity.InfinityCategories.Core.ContractibleKan
public import SerrePositivity.InfinityCategories.Core.JoinBoundary
public import SerrePositivity.InfinityCategories.Core.TerminalVertices
public import Mathlib.Tactic.CrossRefAttribute

/-!
始対象の頂点が張る全部分複体の可縮性。Kerodon 4.7.3.14（Tag 02HM）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open _root_.SerrePositivity.InfinityCategories

/-- 概要：始対象の頂点が張る全部分複体は非空なら可縮。
方針：正次元の境界の最初の頂点で充填し、全頂点が元の境界に属すことを使う。
規約：周囲の単体集合に充填性を仮定しない。
使われ方：固定右の普遍単位の全高次の可縮性。 -/
@[kerodon 02HM]
lemma initialVertices_isContractibleKan {X : SSet.{u}}
    (hne : ∃ x : X _⦋0⦌, IsInitialVertex x) :
    IsContractibleKan (fullSubcomplexOnVertices X IsInitialVertex : SSet.{u}) := by
  intro n b
  cases n with
  | zero =>
    obtain ⟨x, hx⟩ := hne
    let t : (fullSubcomplexOnVertices X IsInitialVertex : SSet.{u}) _⦋0⦌ := ⟨x, by
      intro v
      have hv : v = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
      simpa only [hv, op_id, CategoryTheory.Functor.map_id_apply] using hx⟩
    exact ⟨SSet.const t, boundary.hom_ext₀⟩
  | succ n =>
    let b' := b ≫ (fullSubcomplexOnVertices X IsInitialVertex).ι
    let x := SSet.yonedaEquiv (boundaryVertex n 0 ≫ b')
    have hx : IsInitialVertex x := fullSubcomplexOnVertices_vertex
      (SSet.yonedaEquiv (boundaryVertex n 0 ≫ b))
    obtain ⟨F, hF⟩ := hx n b' (SSet.yonedaEquiv.symm_apply_apply _).symm
    have hv (v : ⦋0⦌ ⟶ ⦋n + 1⦌) :
        IsInitialVertex (SSet.yonedaEquiv (SSet.stdSimplex.map v ≫ F)) := by
      have he : SSet.stdSimplex.map v =
          boundaryVertex n (v.toOrderHom 0) ≫ (boundary (n + 1)).ι := by
        rw [boundaryVertex_ι]
        apply SSet.yonedaEquiv.injective
        rw [Equiv.apply_symm_apply]
        apply SSet.stdSimplex.ext
        intro i
        fin_cases i
        rfl
      rw [he, Category.assoc, hF]
      exact fullSubcomplexOnVertices_vertex
        (SSet.yonedaEquiv (boundaryVertex n (v.toOrderHom 0) ≫ b))
    refine ⟨fullSubcomplexLiftSimplex IsInitialVertex F hv, ?_⟩
    apply (cancel_mono (fullSubcomplexOnVertices X IsInitialVertex).ι).1
    change (boundary (n + 1)).ι ≫ fullSubcomplexLiftSimplex IsInitialVertex F hv ≫
      (fullSubcomplexOnVertices X IsInitialVertex).ι = b'
    rw [fullSubcomplexLiftSimplex_ι]
    exact hF

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
