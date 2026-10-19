module

public import SerrePositivity.KST.Spectra.PointedMappingComponents
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
概要：二つの upstairs 辺を固定して、指定された downstairs 合成三角形を持ち上げる。
方針：二辺を内二次元ホーンへ貼り、Kan fibration の同じホーンへの RLP を使う。
規約：三角形全体の射影を保持。使われ方：境界区間を厳密に保つ比較区間の合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra

/-- 二辺を保持し、指定した三角形全体を同じ射影へ厳密に持ち上げる。 -/
lemma exists_composition_triangle_lift {E B : SSet.{u}} (p : E ⟶ B)
    (hp : SSet.modelCategoryQuillen.J.rlp p) {x y z : E _⦋0⦌}
    (f : E.Edge x y) (g : E.Edge y z) (φ : (Δ[2] : SSet.{u}) ⟶ B)
    (hf : SSet.yonedaEquiv.symm f.edge ≫ p = stdSimplex.δ (2 : Fin 3) ≫ φ)
    (hg : SSet.yonedaEquiv.symm g.edge ≫ p = stdSimplex.δ (0 : Fin 3) ≫ φ) :
    ∃ e : E.Edge x z, ∃ t : SSet.Edge.CompStruct f g e,
      SSet.yonedaEquiv.symm t.simplex ≫ p = φ := by
  have hc : stdSimplex.δ (0 : Fin 2) ≫ SSet.yonedaEquiv.symm f.edge =
      stdSimplex.δ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm g.edge := by
    rw [SSet.Edge.δ_zero_yonedaEquiv_symm, SSet.Edge.δ_one_yonedaEquiv_symm]
  let a := horn₂₁.isPushout.desc (SSet.yonedaEquiv.symm f.edge)
    (SSet.yonedaEquiv.symm g.edge) hc
  have hw : a ≫ p = (horn 2 (1 : Fin 3)).ι ≫ φ := by
    apply horn₂₁.isPushout.hom_ext
    · rw [← Category.assoc, horn₂₁.isPushout.inl_desc, ← Category.assoc, horn.ι_ι]
      exact hf
    · rw [← Category.assoc, horn₂₁.isPushout.inr_desc, ← Category.assoc, horn.ι_ι]
      exact hg
  let hornLift : HasLiftingProperty (horn 2 (1 : Fin 3)).ι p :=
    hp _ (SSet.modelCategoryQuillen.horn_ι_mem_J 2 1)
  let sq : CommSq a (horn 2 (1 : Fin 3)).ι p φ := ⟨hw⟩
  let ψ := sq.lift
  have h₂ : stdSimplex.δ (2 : Fin 3) ≫ ψ = SSet.yonedaEquiv.symm f.edge := by
    rw [← horn.ι_ι_assoc (1 : Fin 3) (2 : Fin 3) (by decide), sq.fac_left]
    exact horn₂₁.isPushout.inl_desc _ _ _
  have h₀ : stdSimplex.δ (0 : Fin 3) ≫ ψ = SSet.yonedaEquiv.symm g.edge := by
    rw [← horn.ι_ι_assoc (1 : Fin 3) (0 : Fin 3) (by decide), sq.fac_left]
    exact horn₂₁.isPushout.inr_desc _ _ _
  have hd₁ : stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) =
      stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) :=
    stdSimplex.δ_comp_δ_self (i := (1 : Fin 2))
  have hd₀ : stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) =
      stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) :=
    stdSimplex.δ_comp_δ (i := (0 : Fin 2)) (j := (0 : Fin 2)) (by decide)
  let e : E.Edge x z := SSet.Edge.mk (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ ψ))
    (by
      rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc,
        hd₁, Category.assoc, h₂, stdSimplex.yonedaEquiv_δ_comp,
        Equiv.apply_symm_apply]
      exact f.src_eq)
    (by
      rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc,
        hd₀,
        Category.assoc, h₀, stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
      exact g.tgt_eq)
  let t : SSet.Edge.CompStruct f g e := {
    simplex := SSet.yonedaEquiv ψ
    d₂ := by
      change E.δ (2 : Fin 3) (SSet.yonedaEquiv ψ) = f.edge
      rw [← stdSimplex.yonedaEquiv_δ_comp, h₂, Equiv.apply_symm_apply]
    d₀ := by
      change E.δ (0 : Fin 3) (SSet.yonedaEquiv ψ) = g.edge
      rw [← stdSimplex.yonedaEquiv_δ_comp, h₀, Equiv.apply_symm_apply]
    d₁ := by
      change E.δ (1 : Fin 3) (SSet.yonedaEquiv ψ) =
        SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ ψ)
      rw [← stdSimplex.yonedaEquiv_δ_comp] }
  refine ⟨e, t, ?_⟩
  change SSet.yonedaEquiv.symm (SSet.yonedaEquiv ψ) ≫ p = φ
  rw [Equiv.symm_apply_apply]
  exact sq.fac_right

end SerrePositivity.KST.Spectra
