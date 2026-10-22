module

public import SerrePositivity.InfinityCategories.F2.Ind.ConeLastFaceRecovery
public import SerrePositivity.InfinityCategories.F2.Ind.TerminalLastFaceCriterion

/-!
概要：任意の単体集合の右錐の右頂点は終対象。
方針：最後の面の一意な延長を錐の切断の計算で与える。
規約：錐にも左因子にも quasicategory 性を仮定しない。
使われ方：終頂点を持つ小さい部分複体への拡大。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {K : SSet.{u}}

/-- 同じ標準単体からの射の最後の頂点が右頂点となる条件。 -/
lemma coneHom_lastVertex_iff {n : ℕ} (f : (Δ[n] : SSet.{u}) ⟶ join K Δ[0]) :
    lastVertexMap n ≫ f = SSet.yonedaEquiv.symm (coneApex K) ↔
      (SSet.yonedaEquiv f).1.val ≤ n := by
  have h : SSet.yonedaEquiv (lastVertexMap n ≫ f) =
      coneSimplexVertex (SSet.yonedaEquiv f) (Fin.last n) := by
    exact (SSet.yonedaEquiv_naturality _ f).symm
  constructor
  · intro hf
    apply (coneSimplexVertex_eq_apex_iff _ (Fin.last n)).mp
    rw [← h, hf, SSet.yonedaEquiv.apply_symm_apply]
  · intro hf
    apply SSet.yonedaEquiv.injective
    rw [h, SSet.yonedaEquiv.apply_symm_apply]
    exact (coneSimplexVertex_eq_apex_iff _ (Fin.last n)).mpr hf

/-- 任意の左因子の同じ右錐の右頂点は終対象。 -/
lemma coneApex_isTerminalVertex (K : SSet.{u}) : IsTerminalVertex (coneApex K) := by
  apply isTerminalVertex_of_unique_lastFace
  · intro n g
    let t := coneSimplexAppend (SSet.yonedaEquiv g)
    refine ⟨SSet.yonedaEquiv.symm t, ?_, ?_⟩
    · apply SSet.yonedaEquiv.injective
      rw [CosimplicialObject.δ, ← SSet.yonedaEquiv_naturality,
        SSet.yonedaEquiv.apply_symm_apply]
      exact coneSimplexAppend_lastFace _
    · apply (coneHom_lastVertex_iff _).mpr
      rw [SSet.yonedaEquiv.apply_symm_apply]
      exact Nat.le_of_lt_succ (SSet.yonedaEquiv g).1.isLt
  · intro n f g hf hg hfg
    apply SSet.yonedaEquiv.injective
    apply coneLastFace_injective ((coneHom_lastVertex_iff f).mp hf)
      ((coneHom_lastVertex_iff g).mp hg)
    rw [SSet.yonedaEquiv_naturality, SSet.yonedaEquiv_naturality]
    exact congrArg SSet.yonedaEquiv hfg

end SerrePositivity.InfinityCategories.F2.Ind
