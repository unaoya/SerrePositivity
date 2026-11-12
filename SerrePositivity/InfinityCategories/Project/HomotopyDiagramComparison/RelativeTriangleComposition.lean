module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PointHomRestrictionComparison
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
概要：inner fibration 上で、指定した底の合成三角形を保って二辺を合成する。
方針：二つの連続する辺を内側二ホーンに貼り、指定した底の二単体に対して持ち上げる。
規約：合成辺の底も二単体も厳密に保持。使われ方：右枝の fiber 内の修正を頂点輸送の辺へ織り込む。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 指定した底の合成三角形を保つ、全空間の実際の合成辺と三角形が存在。 -/
lemma exists_compStruct_over_innerFibration {E B : SSet.{u}} (p : E ⟶ B) [InnerFibration p]
    {x₀ x₁ x₂ : E _⦋0⦌} (a : E.Edge x₀ x₁) (b : E.Edge x₁ x₂)
    (v : B.Edge (p.app _ x₀) (p.app _ x₂))
    (t : SSet.Edge.CompStruct (a.map p) (b.map p) v) :
    ∃ (c : E.Edge x₀ x₂) (s : SSet.Edge.CompStruct a b c),
      (c.map p).edge = v.edge ∧ p.app (Opposite.op ⦋2⦌) s.simplex = t.simplex := by
  let fs : ∀ (j : Fin 3) (_ : j ≠ 1), (Δ[1] : SSet.{u}) ⟶ E :=
    fun j _ ↦ if j = 0 then SSet.yonedaEquiv.symm b.edge else SSet.yonedaEquiv.symm a.edge
  have hf : horn.IsCompatible fs := by
    rw [horn.isCompatible_iff]
    intro j k hj hk hjk
    fin_cases j <;> fin_cases k
    all_goals try norm_num at hj
    all_goals try norm_num at hk
    all_goals try norm_num at hjk
    change stdSimplex.δ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm b.edge =
      stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm a.edge
    rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm,
      b.src_eq, a.tgt_eq]
  let f := hf.desc
  let g := SSet.yonedaEquiv.symm t.simplex
  have hw : f ≫ p = (horn 2 1).ι ≫ g := by
    apply horn.hom_ext'
    intro j hj
    rw [← Category.assoc, horn.IsCompatible.ι_desc, horn.ι_ι_assoc]
    fin_cases j
    · change SSet.yonedaEquiv.symm b.edge ≫ p = stdSimplex.δ (0 : Fin 3) ≫ g
      rw [SSet.yonedaEquiv_symm_comp, stdSimplex.δ_comp_yonedaEquiv_symm, t.d₀]
      rfl
    · exact (hj rfl).elim
    · change SSet.yonedaEquiv.symm a.edge ≫ p = stdSimplex.δ (2 : Fin 3) ≫ g
      rw [SSet.yonedaEquiv_symm_comp, stdSimplex.δ_comp_yonedaEquiv_symm, t.d₂]
      rfl
  have : HasLiftingProperty (horn 2 (1 : Fin 3)).ι p :=
    InnerFibration.mem _ (horn_ι_mem_innerHornInclusions (by decide) (by decide))
  let sq : CommSq f (horn 2 (1 : Fin 3)).ι p g := ⟨hw⟩
  let s := SSet.yonedaEquiv sq.lift
  have hs₂ : E.δ 2 s = a.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← horn.ι_ι_assoc (1 : Fin 3) 2 (by decide),
      sq.fac_left, horn.IsCompatible.ι_desc]
    simp [fs]
  have hs₀ : E.δ 0 s = b.edge := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← horn.ι_ι_assoc (1 : Fin 3) 0 (by decide),
      sq.fac_left, horn.IsCompatible.ι_desc]
    simp [fs]
  have hsrc : E.δ 1 (E.δ 1 s) = x₀ := by
    have he : E.δ 1 (E.δ 1 s) = E.δ 1 (E.δ 2 s) := by
      simp only [SimplicialObject.δ, ← Functor.map_comp_apply, ← op_comp]
      apply congrArg (fun α : ⦋0⦌ ⟶ ⦋2⦌ ↦ E.map α.op s)
      decide
    rw [he, hs₂, a.src_eq]
  have htgt : E.δ 0 (E.δ 1 s) = x₂ := by
    have he : E.δ 0 (E.δ 1 s) = E.δ 0 (E.δ 0 s) := by
      simp only [SimplicialObject.δ, ← Functor.map_comp_apply, ← op_comp]
      apply congrArg (fun α : ⦋0⦌ ⟶ ⦋2⦌ ↦ E.map α.op s)
      decide
    rw [he, hs₀, b.tgt_eq]
  let c : E.Edge x₀ x₂ := ⟨E.δ 1 s, hsrc, htgt⟩
  have hsp : p.app (Opposite.op ⦋2⦌) s = t.simplex := by
    rw [← SSet.yonedaEquiv_comp, sq.fac_right]
    exact Equiv.apply_symm_apply _ _
  refine ⟨c, ⟨s, hs₂, hs₀, rfl⟩, ?_, hsp⟩
  change p.app (Opposite.op ⦋1⦌) (E.δ 1 s) = v.edge
  change p.app _ (E.map (SimplexCategory.δ (1 : Fin 3)).op s) = _
  rw [p.naturality_apply (SimplexCategory.δ (1 : Fin 3)).op s, hsp]
  exact t.d₁

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
