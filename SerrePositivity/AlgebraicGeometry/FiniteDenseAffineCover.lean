module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Irreducible

/-!
概要：空でない有限 affine 開被覆と、既約な場合の稠密な共通の開を実際に供給する。
方針：finiteSubcover が選ぶ点を用い、有限個の空でない開の交叉を取る。
規約：被覆と共通の開は対象から構成し、存在を仮定しない。
使われ方：C06 の Noether な既約成分での Chow の構成の入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits TopologicalSpace
universe u

/-- 空でない準コンパクトなスキームは、Fin n の空でない affine 開による実際の有限被覆を持つ。 -/
theorem exists_finite_nonempty_affine_open_cover (X : Scheme.{u})
    [CompactSpace X] [Nonempty X] :
    ∃ (n : ℕ) (_ : 0 < n) (U : Fin n → X.Opens),
      (∀ i, IsAffineOpen (U i)) ∧ (∀ i, (U i : Set X).Nonempty) ∧ (⨆ i, U i) = ⊤ := by
  classical
  let 𝒰 := X.affineCover.finiteSubcover
  haveI (a : 𝒰.I₀) : IsAffine (𝒰.X a) := by
    dsimp only [𝒰]
    rw [Scheme.OpenCover.finiteSubcover_X]
    infer_instance
  have hne (a : 𝒰.I₀) : ((𝒰.f a).opensRange : Set X).Nonempty := by
    change (Set.range (X.affineCover.f (X.affineCover.idx a.val))).Nonempty
    exact ⟨a.val, X.affineCover.covers a.val⟩
  haveI : Nonempty 𝒰.I₀ := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    obtain ⟨a, _, _⟩ := 𝒰.exists_eq x
    exact ⟨a⟩
  let e := Fintype.equivFin 𝒰.I₀
  let U (i : Fin (Fintype.card 𝒰.I₀)) := (𝒰.f (e.symm i)).opensRange
  refine ⟨Fintype.card 𝒰.I₀, Fintype.card_pos, U,
    (fun i ↦ isAffineOpen_opensRange (𝒰.f (e.symm i))), (fun i ↦ hne (e.symm i)), ?_⟩
  change (⨆ i, (𝒰.f (e.symm i)).opensRange) = ⊤
  exact (e.symm.iSup_comp (g := fun a : 𝒰.I₀ ↦ (𝒰.f a).opensRange)).trans 𝒰.iSup_opensRange

/-- 既約な空間の有限個の空でない開の共通部分は空でない。 -/
theorem finite_open_iInf_nonempty {X : Type u} [TopologicalSpace X] [IrreducibleSpace X]
    (n : ℕ) (U : Fin n → Opens X) (hne : ∀ i, (U i : Set X).Nonempty) :
    ((⨅ i, U i : Opens X) : Set X).Nonempty := by
  induction n with
  | zero => simpa using (Set.univ_nonempty : (Set.univ : Set X).Nonempty)
  | succ n ih =>
      have hsplit : (⨅ i : Fin (n + 1), U i) = U 0 ⊓ ⨅ j : Fin n, U j.succ := by
        apply le_antisymm
        · exact le_inf (iInf_le U 0) (le_iInf fun j ↦ iInf_le U j.succ)
        · apply le_iInf
          intro i
          refine Fin.cases ?_ (fun j ↦ ?_) i
          · exact inf_le_left
          · exact inf_le_right.trans (iInf_le _ j)
      rw [hsplit, Opens.coe_inf]
      exact nonempty_preirreducible_inter (U 0).isOpen (⨅ i : Fin n, U i.succ).isOpen
        (hne 0) (ih (fun i ↦ U i.succ) (fun i ↦ hne i.succ))

/-- 準コンパクトな既約スキームは、稠密な共通の開を持つ実際の有限 affine 被覆を持つ。 -/
theorem exists_dense_common_finite_affine_cover (X : Scheme.{u})
    [CompactSpace X] [IrreducibleSpace X] :
    ∃ (n : ℕ) (_ : 0 < n) (U : Fin n → X.Opens) (W : X.Opens),
      (∀ i, IsAffineOpen (U i)) ∧ (∀ i, (U i : Set X).Nonempty) ∧
        (⨆ i, U i) = ⊤ ∧ Dense (W : Set X) ∧ (W : Set X).Nonempty ∧ ∀ i, W ≤ U i := by
  obtain ⟨n, hn, U, hAff, hne, hcover⟩ := exists_finite_nonempty_affine_open_cover X
  let W := ⨅ i, U i
  have hW : (W : Set X).Nonempty := finite_open_iInf_nonempty n U hne
  exact ⟨n, hn, U, W, hAff, hne, hcover, W.isOpen.dense hW, hW, fun i ↦ iInf_le U i⟩

end SerrePositivity.AlgebraicGeometry
