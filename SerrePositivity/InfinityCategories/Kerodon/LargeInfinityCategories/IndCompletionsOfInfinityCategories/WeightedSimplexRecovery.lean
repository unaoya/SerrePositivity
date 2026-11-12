module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.WeightedCoefficientMap
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.WeightedBoundaryLift

/-!
概要：weighted 単体の同一性と、その同じ単体上の最後の係数評価。
方針：最後の面と最後の成分で図式を決め、係数評価の制限公式を使う。
規約：係数の充填性は不要。使われ方：指定した自然変換の像を保つ境界充填。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {I : Type u} [Category.{u} I] (F : I ⥤ SSet.{u})

/-- weighted 単体の図式は、最後の面と最後の成分で決まる。 -/
lemma weightedDiagram_eq_of_prefix_and_last {n : ℕ} (σ : ComposableArrows I (n + 1))
    (φ ψ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight (n + 1) ⟶ σ ⋙ F)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) ⟨σ, φ⟩ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap F
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) ⟨σ, ψ⟩)
    (ht : φ.app (Fin.last (n + 1)) = ψ.app (Fin.last (n + 1))) : φ = ψ := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveDiagram_ext _ ht
  intro i
  have h := NatTrans.congr_app (eq_of_heq (Sigma.mk.inj hp).2) i
  change stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) i) ≫ φ.app i.castSucc =
    stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) i) ≫ ψ.app i.castSucc at h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction_inclusion, CategoryTheory.Functor.map_id,
    Category.id_comp] at h
  exact h

/-- 同じ境界と最後の係数を持つ二つの weighted 単体は等しい。 -/
lemma weightedDiagram_eq_of_boundary_and_last {n : ℕ} (σ : ComposableArrows I (n + 1))
    (φ ψ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight (n + 1) ⟶ σ ⋙ F)
    (hb : (boundary (n + 1)).ι ≫ (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F)).symm
        (⟨σ, φ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F (n + 1)) =
      (boundary (n + 1)).ι ≫ (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F)).symm
        (⟨σ, ψ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F (n + 1)))
    (ht : φ.app (Fin.last (n + 1)) = ψ.app (Fin.last (n + 1))) : φ = ψ := by
  apply weightedDiagram_eq_of_prefix_and_last F σ φ ψ _ ht
  apply (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F) (n := ⦋n⦌)).symm.injective
  have hp := congrArg (fun q ↦ boundary.ι (Fin.last (n + 1)) ≫ q) hb
  rw [← Category.assoc, ← Category.assoc, boundary.ι_ι] at hp
  have hφ := SSet.yonedaEquiv_symm_naturality_left (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n (n + 1) (Nat.le_succ n))
    (⟨σ, φ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F (n + 1))
  have hψ := SSet.yonedaEquiv_symm_naturality_left (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n (n + 1) (Nat.le_succ n))
    (⟨σ, ψ⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F (n + 1))
  have hp' : stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) ≫
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F)).symm ⟨σ, φ⟩ =
    stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n (n + 1) (Nat.le_succ n)) ≫
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F)).symm ⟨σ, ψ⟩ := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion_eq_lastFace]
    exact hp
  exact hφ.symm.trans (hp'.trans hψ)

/-- 元の単体上の最後の係数評価は、元の最後の成分そのもの。 -/
lemma weightedSimplexCoefficient_self {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F n)
    (h : SSet.yonedaEquiv.symm s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F =
      (𝟙 (Δ[n] : SSet.{u})) ≫ SSet.yonedaEquiv.symm s.1) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient F s.1 (SSet.yonedaEquiv.symm s) (𝟙 _) h =
      s.2.app (Fin.last n) := by
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient_diagram F s.1 (𝟙 ⦋n⦌) s.2 h
  change _ = s.2.app (Fin.last n) ≫
    F.map (s.1.map (homOfLE (Fin.le_last (Fin.last n)))) at he
  have hid : F.map (s.1.map (homOfLE (Fin.le_last (Fin.last n)))) = 𝟙 _ := by
    rw [show homOfLE (Fin.le_last (Fin.last n)) = 𝟙 (Fin.last n) from
      Subsingleton.elim _ _, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  exact he.trans ((congrArg (fun q ↦ s.2.app (Fin.last n) ≫ q) hid).trans
    (Category.comp_id _))

/-- 任意のパラメータで制限した同じ単体の係数評価も、同じ最後の成分の制限。 -/
lemma weightedSimplexCoefficient_restrict_self {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex F n)
    {T : SSet.{u}} (r : T ⟶ (Δ[n] : SSet.{u}))
    (h : (r ≫ SSet.yonedaEquiv.symm s) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F =
      r ≫ SSet.yonedaEquiv.symm s.1) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient F s.1 (r ≫ SSet.yonedaEquiv.symm s) r h =
      r ≫ s.2.app (Fin.last n) := by
  have hs : SSet.yonedaEquiv.symm s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F =
      (𝟙 (Δ[n] : SSet.{u})) ≫ SSet.yonedaEquiv.symm s.1 := by
    rw [Category.id_comp, SSet.yonedaEquiv_symm_comp]
    rfl
  have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexCoefficient_precomp F s.1
    (SSet.yonedaEquiv.symm s) (𝟙 _) hs r (by simpa only [Category.comp_id] using h)
  rw [weightedSimplexCoefficient_self F s hs] at hp
  simpa only [Category.comp_id] using hp

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
