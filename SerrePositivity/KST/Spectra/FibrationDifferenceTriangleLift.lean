module

public import SerrePositivity.KST.Spectra.PointedMappingComponents
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
概要：共通の始点を持つ二辺を固定し、指定された比較三角形全体を持ち上げる。
方針：二辺を外二次元ホーンへ貼り、Kan fibration の同じホーンへの RLP を使う。
規約：三角形全体の射影を保持。使われ方：共有する非定数辺を消去する相対比較。
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
lemma exists_difference_triangle_lift {E B : SSet.{u}} (p : E ⟶ B)
    (hp : SSet.modelCategoryQuillen.J.rlp p) {x y z : E _⦋0⦌}
    (f : E.Edge x y) (g : E.Edge x z) (φ : (Δ[2] : SSet.{u}) ⟶ B)
    (hf : SSet.yonedaEquiv.symm f.edge ≫ p = stdSimplex.δ (2 : Fin 3) ≫ φ)
    (hg : SSet.yonedaEquiv.symm g.edge ≫ p = stdSimplex.δ (1 : Fin 3) ≫ φ) :
    ∃ e : E.Edge y z, ∃ t : SSet.Edge.CompStruct f e g,
      SSet.yonedaEquiv.symm t.simplex ≫ p = φ := by
  have hc : stdSimplex.δ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm f.edge =
      stdSimplex.δ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm g.edge := by
    rw [SSet.Edge.δ_one_yonedaEquiv_symm, SSet.Edge.δ_one_yonedaEquiv_symm]
  let a := horn₂₀.isPushout.desc (SSet.yonedaEquiv.symm f.edge)
    (SSet.yonedaEquiv.symm g.edge) hc
  have hw : a ≫ p = (horn 2 (0 : Fin 3)).ι ≫ φ := by
    apply horn₂₀.isPushout.hom_ext
    · rw [← Category.assoc, horn₂₀.isPushout.inl_desc, ← Category.assoc, horn.ι_ι]
      exact hf
    · rw [← Category.assoc, horn₂₀.isPushout.inr_desc, ← Category.assoc, horn.ι_ι]
      exact hg
  let hornLift : HasLiftingProperty (horn 2 (0 : Fin 3)).ι p :=
    hp _ (SSet.modelCategoryQuillen.horn_ι_mem_J 2 0)
  let sq : CommSq a (horn 2 (0 : Fin 3)).ι p φ := ⟨hw⟩
  let ψ := sq.lift
  have h₂ : stdSimplex.δ (2 : Fin 3) ≫ ψ = SSet.yonedaEquiv.symm f.edge := by
    rw [← horn.ι_ι_assoc (0 : Fin 3) (2 : Fin 3) (by decide), sq.fac_left]
    exact horn₂₀.isPushout.inl_desc _ _ _
  have h₁ : stdSimplex.δ (1 : Fin 3) ≫ ψ = SSet.yonedaEquiv.symm g.edge := by
    rw [← horn.ι_ι_assoc (0 : Fin 3) (1 : Fin 3) (by decide), sq.fac_left]
    exact horn₂₀.isPushout.inr_desc _ _ _
  have hd₁ : stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) =
      stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) :=
    (stdSimplex.δ_comp_δ (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)).symm
  have hd₀ : stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) =
      stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) :=
    (stdSimplex.δ_comp_δ (i := (0 : Fin 2)) (j := (0 : Fin 2)) (by decide)).symm
  let e : E.Edge y z := SSet.Edge.mk (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ ψ))
    (by
      rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc,
        hd₁, Category.assoc, h₂, stdSimplex.yonedaEquiv_δ_comp,
        Equiv.apply_symm_apply]
      exact f.tgt_eq)
    (by
      rw [← stdSimplex.yonedaEquiv_δ_comp, ← Category.assoc,
        hd₀,
        Category.assoc, h₁, stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
      exact g.tgt_eq)
  let t : SSet.Edge.CompStruct f e g := {
    simplex := SSet.yonedaEquiv ψ
    d₂ := by
      change E.δ (2 : Fin 3) (SSet.yonedaEquiv ψ) = f.edge
      rw [← stdSimplex.yonedaEquiv_δ_comp, h₂, Equiv.apply_symm_apply]
    d₀ := by
      change E.δ (0 : Fin 3) (SSet.yonedaEquiv ψ) =
        SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ ψ)
      rw [← stdSimplex.yonedaEquiv_δ_comp]
    d₁ := by
      change E.δ (1 : Fin 3) (SSet.yonedaEquiv ψ) = g.edge
      rw [← stdSimplex.yonedaEquiv_δ_comp, h₁, Equiv.apply_symm_apply] }
  refine ⟨e, t, ?_⟩
  change SSet.yonedaEquiv.symm (SSet.yonedaEquiv ψ) ≫ p = φ
  rw [Equiv.symm_apply_apply]
  exact sq.fac_right

end SerrePositivity.KST.Spectra
