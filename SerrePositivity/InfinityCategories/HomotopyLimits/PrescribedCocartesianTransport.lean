module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PrescribedCartesianTransport
public import SerrePositivity.InfinityCategories.F1B.KanCocartesianHornFibrationComparison

/-!
概要：元の全頂点の辺を固定した cocartesian 輸送 prism を構成する。
方針：全頂点の相対延長と cocartesian transport の選択の一意性を使う。
規約：元の指定された置換辺を変更しない。使われ方：HTT 5.2.4.6 の cf 比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 元の全頂点の辺を変更せず、同じ始点・底を持つ cocartesian prism へ延長する。 -/
lemma exists_cocartesianPrism_prescribed_vertices {A E : SSet.{u}}
    (p : E ⟶ (Δ[1] : SSet.{u})) [CocartesianFibration p] (f : A ⟶ E)
    (hf : f ≫ p = SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (x : A _⦋0⦌ → E _⦋0⦌)
    (e : ∀ v, E.Edge (f.app (Opposite.op ⦋0⦌) v) (x v))
    (he : ∀ v, p.app (Opposite.op ⦋1⦌) (e v).edge = homotopyIntervalEdge.edge)
    (hc : ∀ v, IsCocartesianEdge p (e v).edge) :
    ∃ H : (Δ[1] : SSet.{u}) ⊗ A ⟶ E,
      prismEndpoint 0 A ≫ H = f ∧ H ≫ p = fst (Δ[1] : SSet.{u}) A ∧
      (∀ v : A _⦋0⦌, IsCocartesianEdge p (H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant v 1))) ∧
      (∀ v : A _⦋0⦌, H.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant v 1) = (e v).edge) := by
  let g := vertexEdgeFamily (fun v ↦ SSet.yonedaEquiv.symm (e v).edge)
  have ht : prismEndpoint 0 (vertexDiscrete A) ≫ g = vertexDiscreteι A ≫ f := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro v
    change (SSet.yonedaEquiv.symm (e v).edge).app (Opposite.op ⦋n⦌)
      (PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) n) =
      f.app (Opposite.op ⦋n⦌) (PinchedHom.constant v n)
    rw [pinchedConstant_map, pinchedConstant_map]
    congr 1
    have htgt := stdSimplex.yonedaEquiv_δ_comp (SSet.yonedaEquiv.symm (e v).edge) 1
    simp only [stdSimplex.δ_one_eq_const, SSet.const_comp, SSet.yonedaEquiv_const,
      Equiv.apply_symm_apply] at htgt
    exact htgt.trans (e v).src_eq
  have hb : g ≫ p = (Δ[1] ◁ vertexDiscreteι A) ≫ fst (Δ[1] : SSet.{u}) A := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨t, v⟩
    change ((SSet.yonedaEquiv.symm (e v).edge) ≫ p).app n t = t
    have h := congrArg SSet.yonedaEquiv.symm (he v)
    rw [← SSet.yonedaEquiv_symm_comp] at h
    rw [h]
    have hi : SSet.yonedaEquiv.symm homotopyIntervalEdge.edge =
        (𝟙 (Δ[1] : SSet.{u})) := by
      apply SSet.yonedaEquiv.injective
      rw [Equiv.apply_symm_apply]
      apply SSet.stdSimplex.ext
      intro i
      fin_cases i <;> rfl
    rw [hi]
    rfl
  have hg : ∀ v : (vertexDiscrete A) _⦋0⦌, IsCocartesianEdge p
      (g.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant v 1)) := by
    intro v
    change IsCocartesianEdge p ((SSet.yonedaEquiv.symm (e v).edge).app _
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))))
    rw [SSet.yonedaEquiv_symm_app_id]
    exact hc v
  have := CocartesianFibration.toCocartesianHornFibration p
  obtain ⟨H, hH, h0, hp, hcart⟩ := cocartesianHomotopy_extend p (vertexDiscreteι A) g f
    (fst (Δ[1] : SSet.{u}) A) ht (by simpa only [prismEndpoint, lift_fst] using hf) hb
    (fun v ↦ (isCocartesianEdge_iff_hasCocartesianHornLifting p _).1 (hg v))
  refine ⟨H, h0, hp, ?_, ?_⟩
  · intro v
    exact (isCocartesianEdge_iff_hasCocartesianHornLifting p _).2 (hcart v)
  · intro v
    have h := congrArg (fun k ↦ k.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), v)) hH
    change H.app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant v 1) =
        (SSet.yonedaEquiv.symm (e v).edge).app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) at h
    rwa [SSet.yonedaEquiv_symm_app_id] at h

end
end SerrePositivity.InfinityCategories.HomotopyLimits
