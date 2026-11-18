module

public import SerrePositivity.InfinityCategories.Project.SetWeightedTensors.SetElements
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveLeftFibration

/-!
概要：集合係数の taut scaffold は同型なので、weighted nerve の左ファイブレーション性を元の要素圏の射影に移す。
方針：元の相対写像の射影と指定された比較を保つ。
使われ方：R06.2 の始点側の添字比較。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets
open SerrePositivity.InfinityCategories.Project.SetWeightedTensors



namespace SerrePositivity.InfinityCategories.Project.SetWeightedTensors

private def discreteLabel {T : Type u} {n : ℕ}
    (a : (Δ[n] : SSet.{u}) ⟶ discrete T) : T :=
  SSet.yonedaEquiv (n := ⦋n⦌) a

private theorem discrete_stdSimplex_const {T : Type u} {n : ℕ}
    (a : (Δ[n] : SSet.{u}) ⟶ discrete T) :
    (SSet.const (Y := discrete T) (discreteLabel a)) = a := by
  apply SSet.yonedaEquiv.injective
  rfl

private theorem hom_eq_of_discrete_point {T : Type u} {n : ℕ}
    (k : (Δ[0] : SSet.{u}) ⟶ Δ[n]) (a b : (Δ[n] : SSet.{u}) ⟶ discrete T)
    (h : k ≫ a = k ≫ b) : a = b := by
  have ha := discrete_stdSimplex_const a
  have hb := discrete_stdSimplex_const b
  have hc : (SSet.const (X := (Δ[0] : SSet.{u})) (Y := discrete T) (discreteLabel a)) =
      SSet.const (discreteLabel b) := by
    rw [← SSet.comp_const k, ← SSet.comp_const k, ha, hb]
    exact h
  have hd : discreteLabel a = discreteLabel b :=
    congrArg (SSet.yonedaEquiv (n := ⦋0⦌)) hc
  exact ha.symm.trans ((congrArg
      (fun t => (SSet.const (Y := discrete T) t : (Δ[n] : SSet.{u}) ⟶ _)) hd).trans hb)

private theorem coefficient_initial_identity {D : Type u} [SmallCategory D]
    (P : D ⥤ Type u) {n : ℕ} (σ : ComposableArrows D n) :
    (coefficients P).map (σ.map (homOfLE (Fin.zero_le (0 : Fin (n + 1))))) =
      𝟙 ((coefficients P).obj (σ.obj 0)) := by
  have h : homOfLE (Fin.zero_le (0 : Fin (n + 1))) = 𝟙 (0 : Fin (n + 1)) :=
    Subsingleton.elim _ _
  exact (congrArg (fun f ↦ (coefficients P).map (σ.map f)) h).trans
    ((congrArg (fun f ↦ (coefficients P).map f) (σ.map_id 0)).trans
      ((coefficients P).map_id (σ.obj 0)))

private theorem tautScaffold_discrete_isIso {D : Type u} [SmallCategory D] (P : D ⥤ Type u) :
    IsIso (tautScaffold (coefficients P)) := by
  apply (NatTrans.isIso_iff_isIso_app _).2
  rintro ⟨⟨n⟩⟩
  apply (isIso_iff_bijective _).2
  constructor
  · rintro ⟨σ, a⟩ ⟨τ, b⟩ hab
    have hσ : σ = τ := congrArg Sigma.fst hab
    subst τ
    have hψ : tautScaffoldDiagram (coefficients P) ⟨σ, a⟩ =
        tautScaffoldDiagram (coefficients P) ⟨σ, b⟩ :=
      eq_of_heq (Sigma.mk.inj_iff.mp hab).2
    refine Sigma.ext rfl (heq_of_eq ?_)
    have h₀ := congrArg (fun α => α.app (0 : Fin (n + 1))) hψ
    change stdSimplex.map (simplexPrefixInclusion 0 n (Nat.zero_le n)) ≫ a ≫
        (coefficients P).map (σ.map (homOfLE (Fin.zero_le 0))) =
      stdSimplex.map (simplexPrefixInclusion 0 n (Nat.zero_le n)) ≫ b ≫
        (coefficients P).map (σ.map (homOfLE (Fin.zero_le 0))) at h₀
    rw [coefficient_initial_identity P σ] at h₀
    simp only [Category.comp_id] at h₀
    exact hom_eq_of_discrete_point _ a b h₀
  · rintro ⟨σ, ψ⟩
    let a : Δ[n] ⟶ (coefficients P).obj (σ.obj 0) :=
      SSet.const (SSet.yonedaEquiv (ψ.app 0))
    refine ⟨⟨σ, a⟩, Sigma.ext rfl (heq_of_eq ?_)⟩
    apply NatTrans.ext
    funext i
    have h₀ : (SSet.const (SSet.yonedaEquiv (ψ.app 0)) :
        (Δ[0] : SSet.{u}) ⟶ (coefficients P).obj (σ.obj 0)) = ψ.app 0 :=
      discrete_stdSimplex_const (ψ.app 0)
    let χ : simplexPrefixWeight n ⟶ σ ⋙ coefficients P :=
      tautScaffoldDiagram (coefficients P) ⟨σ, a⟩
    have he : χ.app (0 : Fin (n + 1)) = ψ.app 0 := by
      change _ ≫ a ≫ (coefficients P).map (σ.map (homOfLE (Fin.zero_le 0))) = _
      rw [coefficient_initial_identity P σ, Category.comp_id]
      dsimp only [a]
      rw [SSet.comp_const]
      exact h₀
    change χ.app i = ψ.app i
    let f : (0 : Fin (n + 1)) ⟶ i := homOfLE (Fin.zero_le i)
    apply hom_eq_of_discrete_point ((simplexPrefixWeight n).map f)
    rw [χ.naturality f, ψ.naturality f, he]

/-- 集合係数の taut scaffold は同型なので、weighted nerve の左ファイブレーション性を元の要素圏の射影に移す。
Kerodon Construction 5.3.4.11（Tag 0373）、Theorem 5.3.3.13（Tag 036N）の集合係数での比較。 -/
lemma elements_projection_leftFibration {D : Type u} [SmallCategory D] (P : D ⥤ Type u) :
    LeftFibration (nerveMap (Functor.Elements.π P)) := by
  have : IsIso (tautScaffold (coefficients P)) := tautScaffold_discrete_isIso P
  let k := elementsToReplacement P ≫ tautScaffold (coefficients P)
  have hk : k ≫ weightedNerveProjection (coefficients P) =
      nerveMap (Functor.Elements.π P) := by
    dsimp only [k]
    rw [Category.assoc, tautScaffold_projection, elementsToReplacement_projection]
  let s : Arrow.mk (nerveMap (Functor.Elements.π P)) ≅
      Arrow.mk (weightedNerveProjection (coefficients P)) :=
    Arrow.isoMk (asIso k) (Iso.refl _) (by
      change k ≫ weightedNerveProjection (coefficients P) = _ ≫ 𝟙 _
      rw [Category.comp_id]
      exact hk)
  exact ⟨(leftFibrations.arrow_mk_iso_iff s).mpr (LeftFibration.mem (p := weightedNerveProjection _))⟩

end SerrePositivity.InfinityCategories.Project.SetWeightedTensors
