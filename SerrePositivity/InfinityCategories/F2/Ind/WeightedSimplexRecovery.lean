module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientMap
public import SerrePositivity.InfinityCategories.F2.Ind.WeightedBoundaryLift

/-!
概要：weighted 単体の同一性と、その同じ単体上の最後の係数評価。
方針：最後の面と最後の成分で図式を決め、係数評価の制限公式を使う。
規約：係数の充填性は不要。使われ方：指定した自然変換の像を保つ境界充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {I : Type u} [Category.{u} I] (F : I ⥤ SSet.{u})

/-- weighted 単体の図式は、最後の面と最後の成分で決まる。 -/
lemma weightedDiagram_eq_of_prefix_and_last {n : ℕ} (σ : ComposableArrows I (n + 1))
    (φ ψ : simplexPrefixWeight (n + 1) ⟶ σ ⋙ F)
    (hp : weightedNerveSimplexMap F
        (simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) ⟨σ, φ⟩ =
      weightedNerveSimplexMap F
        (simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) ⟨σ, ψ⟩)
    (ht : φ.app (Fin.last (n + 1)) = ψ.app (Fin.last (n + 1))) : φ = ψ := by
  apply weightedNerveDiagram_ext _ ht
  intro i
  have h := NatTrans.congr_app (eq_of_heq (Sigma.mk.inj hp).2) i
  change stdSimplex.map (simplexPrefixRestriction
      (simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) i) ≫ φ.app i.castSucc =
    stdSimplex.map (simplexPrefixRestriction
      (simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) i) ≫ ψ.app i.castSucc at h
  rw [simplexPrefixRestriction_inclusion, CategoryTheory.Functor.map_id,
    Category.id_comp] at h
  exact h

/-- 同じ境界と最後の係数を持つ二つの weighted 単体は等しい。 -/
lemma weightedDiagram_eq_of_boundary_and_last {n : ℕ} (σ : ComposableArrows I (n + 1))
    (φ ψ : simplexPrefixWeight (n + 1) ⟶ σ ⋙ F)
    (hb : (boundary (n + 1)).ι ≫ (SSet.yonedaEquiv (X := weightedNerve F)).symm
        (⟨σ, φ⟩ : weightedNerveSimplex F (n + 1)) =
      (boundary (n + 1)).ι ≫ (SSet.yonedaEquiv (X := weightedNerve F)).symm
        (⟨σ, ψ⟩ : weightedNerveSimplex F (n + 1)))
    (ht : φ.app (Fin.last (n + 1)) = ψ.app (Fin.last (n + 1))) : φ = ψ := by
  apply weightedDiagram_eq_of_prefix_and_last F σ φ ψ _ ht
  apply (SSet.yonedaEquiv (X := weightedNerve F) (n := ⦋n⦌)).symm.injective
  have hp := congrArg (fun q ↦ boundary.ι (Fin.last (n + 1)) ≫ q) hb
  rw [← Category.assoc, ← Category.assoc, boundary.ι_ι] at hp
  have hφ := SSet.yonedaEquiv_symm_naturality_left (X := weightedNerve F)
    (simplexPrefixInclusion n (n + 1) (Nat.le_succ n))
    (⟨σ, φ⟩ : weightedNerveSimplex F (n + 1))
  have hψ := SSet.yonedaEquiv_symm_naturality_left (X := weightedNerve F)
    (simplexPrefixInclusion n (n + 1) (Nat.le_succ n))
    (⟨σ, ψ⟩ : weightedNerveSimplex F (n + 1))
  have hp' : stdSimplex.map (simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) ≫
      (SSet.yonedaEquiv (X := weightedNerve F)).symm ⟨σ, φ⟩ =
    stdSimplex.map (simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) ≫
      (SSet.yonedaEquiv (X := weightedNerve F)).symm ⟨σ, ψ⟩ := by
    rw [simplexPrefixInclusion_eq_lastFace]
    exact hp
  exact hφ.symm.trans (hp'.trans hψ)

/-- 元の単体上の最後の係数評価は、元の最後の成分そのもの。 -/
lemma weightedSimplexCoefficient_self {n : ℕ} (s : weightedNerveSimplex F n)
    (h : SSet.yonedaEquiv.symm s ≫ weightedNerveProjection F =
      (𝟙 (Δ[n] : SSet.{u})) ≫ SSet.yonedaEquiv.symm s.1) :
    weightedNerveSimplexCoefficient F s.1 (SSet.yonedaEquiv.symm s) (𝟙 _) h =
      s.2.app (Fin.last n) := by
  have he := weightedNerveSimplexCoefficient_diagram F s.1 (𝟙 ⦋n⦌) s.2 h
  change _ = s.2.app (Fin.last n) ≫
    F.map (s.1.map (homOfLE (Fin.le_last (Fin.last n)))) at he
  have hid : F.map (s.1.map (homOfLE (Fin.le_last (Fin.last n)))) = 𝟙 _ := by
    rw [show homOfLE (Fin.le_last (Fin.last n)) = 𝟙 (Fin.last n) from
      Subsingleton.elim _ _, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  exact he.trans ((congrArg (fun q ↦ s.2.app (Fin.last n) ≫ q) hid).trans
    (Category.comp_id _))

/-- 任意のパラメータで制限した同じ単体の係数評価も、同じ最後の成分の制限。 -/
lemma weightedSimplexCoefficient_restrict_self {n : ℕ} (s : weightedNerveSimplex F n)
    {T : SSet.{u}} (r : T ⟶ (Δ[n] : SSet.{u}))
    (h : (r ≫ SSet.yonedaEquiv.symm s) ≫ weightedNerveProjection F =
      r ≫ SSet.yonedaEquiv.symm s.1) :
    weightedNerveSimplexCoefficient F s.1 (r ≫ SSet.yonedaEquiv.symm s) r h =
      r ≫ s.2.app (Fin.last n) := by
  have hs : SSet.yonedaEquiv.symm s ≫ weightedNerveProjection F =
      (𝟙 (Δ[n] : SSet.{u})) ≫ SSet.yonedaEquiv.symm s.1 := by
    rw [Category.id_comp, SSet.yonedaEquiv_symm_comp]
    rfl
  have hp := weightedNerveSimplexCoefficient_precomp F s.1
    (SSet.yonedaEquiv.symm s) (𝟙 _) hs r (by simpa only [Category.comp_id] using h)
  rw [weightedSimplexCoefficient_self F s hs] at hp
  simpa only [Category.comp_id] using hp

end SerrePositivity.InfinityCategories.F2.Ind
