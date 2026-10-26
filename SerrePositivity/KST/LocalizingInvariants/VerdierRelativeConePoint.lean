module

public import SerrePositivity.KST.LocalizingInvariants.VerdierRelativeConeRecovery
public import SerrePositivity.InfinityCategories.Core.JoinTensorPoint

/-!
概要：一点パラメータの境界付き商錐回収を、元の有限商錐の回収から構成する。
方針：一点との積の射影同型で運び、同じ比較円柱を前合成する。
規約：元の有限境界を全時刻で固定する比較を保持する。
使われ方：c5 の標準単体の次元帰納の基底。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma hasVerdierRelativeConeRecovery_point {A B C : StableCategory.{u}}
    {i : ExactMap A B} {q : ExactMap B C} (h : IsVerdierSequence i q) :
    HasVerdierRelativeConeRecovery q.hom (Δ[0] : SSet.{u}) := by
  intro K _ p H hb
  let r : K ⊗ (Δ[0] : SSet.{u}) ≅ K := asIso (fst K Δ[0])
  let s : join (Δ[0] : SSet.{u}) K ⊗ Δ[0] ≅ join (Δ[0] : SSet.{u}) K :=
    asIso (fst _ Δ[0])
  let j := joinInr (Δ[0] : SSet.{u}) K
  have hn : (j ▷ (Δ[0] : SSet.{u})) ≫ s.hom = r.hom ≫ j := rfl
  have hn' : j ≫ s.inv = r.inv ≫ (j ▷ (Δ[0] : SSet.{u})) := by
    apply (cancel_mono s.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hn, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  let p₀ := r.inv ≫ p
  let t : JoinCone (p₀ ≫ q.hom) := ⟨s.inv ≫ H, by
    rw [← Category.assoc, hn', Category.assoc, hb]
    rfl⟩
  obtain ⟨c, U, hU, hiU⟩ := exists_verdierQuotientConeRelativeComparison h p₀ t
  let D := s.hom ≫ c.val
  let V : SSet.Homotopy (D ≫ q.hom) H := {
    h := (s.hom ▷ (Δ[1] : SSet.{u})) ≫ U.h
    h₀ := by rw [SSet.ι₀_comp_assoc, U.h₀]; rfl
    h₁ := by
      rw [SSet.ι₁_comp_assoc, U.h₁]
      exact Iso.hom_inv_id_assoc s H
    rel := (functorHomotopyPrecomp U s.hom).rel }
  refine ⟨⟨D, ?_, V, ?_, ?_⟩⟩
  · change (j ▷ Δ[0]) ≫ (s.hom ≫ c.val) = p
    rw [← Category.assoc, hn, Category.assoc, c.property]
    exact Iso.hom_inv_id_assoc r p
  · change ((j ▷ Δ[0]) ▷ Δ[1]) ≫ ((s.hom ▷ Δ[1]) ≫ U.h) = _
    rw [← comp_whiskerRight_assoc, hn, comp_whiskerRight, Category.assoc, hU]
    have hp : (r.hom ▷ (Δ[1] : SSet.{u})) ≫ fst K Δ[1] =
        fst (K ⊗ (Δ[0] : SSet.{u})) Δ[1] ≫ r.hom := rfl
    rw [← Category.assoc, hp, Category.assoc]
    change _ ≫ r.hom ≫ r.inv ≫ p ≫ q.hom = _
    rw [Iso.hom_inv_id_assoc]
  · intro x
    have he : (simplicialHomotopyVertexEdge V x).edge =
        (simplicialHomotopyVertexEdge (functorHomotopyPrecomp U s.hom) x).edge := rfl
    apply (isInvertibleEdge_congr he).mpr
    exact (isInvertibleEdge_congr
      (simplicialHomotopyVertexEdge_precomp_edge U s.hom x)).mpr (hiU _)

end SerrePositivity.KST.LocalizingInvariants
