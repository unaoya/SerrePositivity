module

public import SerrePositivity.AlgebraicGeometry.PerfectCechUniversalBaseChange
public import SerrePositivity.AlgebraicGeometry.NilBaseChangePerfectCech
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
概要：nil閉厚化による底変換後の完全構造層の普遍Čech降下性を反映する。
方針：試験基底の同じ閉厚化をその切断環のSpecで表示し、N06を適用する。
規約：元の試験写像と被覆を保持し、Noether性は試験基底だけで使う。
使われ方：被約化とNoether閉像の帰納（承認済み計画D09）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
local notation "up" => ComplexShape.up ℕ
set_option backward.isDefEq.respectTransparency false

/-- 同じnil閉厚化での底変換後から、元の普遍Čech降下性を反映する。 -/
theorem perfectCechUniversalDescent_of_nil_baseChange
    (p : ℕ) (hp : p.Prime) {X Y Y₀ : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [QuasiCompact f] [LocallyOfFinitePresentation f]
    (i : Y₀ ⟶ Y) [IsClosedImmersion i] [Surjective i] [LocallyOfFinitePresentation i]
    (hf : PerfectCechUniversalDescent p hp (pullback.snd f i)) :
    PerfectCechUniversalDescent p hp f := by
  intro R _ _ hR t ι _ _ U hU hcU
  let P := pullback i t
  let b := pullback.snd i t
  letI : IsAffine P := inferInstance
  letI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian b
  let S := Γ(P, ⊤)
  letI : IsNoetherianRing S := IsLocallyNoetherian.component_noetherian (X := P) ⟨⊤, isAffineOpen_top P⟩
  let l := P.isoSpec.inv ≫ pullback.fst i t
  let r := P.isoSpec.inv ≫ b
  let q : R →+* S := b.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have hq : r = Spec.map (CommRingCat.ofHom q) := by
    change P.isoSpec.inv ≫ b =
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ b.appTop)
    rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, Scheme.isoSpec_inv_naturality]
  have hS : (p : S) = 0 := by rw [← map_natCast q, hR, map_zero]
  let g₀ := pullback.snd f i
  let g := pullback.snd f t
  let g₁ := pullback.snd g₀ l
  let a := pullback.fst g₀ l ≫ pullback.fst f i
  have hbase : IsPullback l r i t :=
    (IsPullback.of_hasPullback i t).of_iso' P.isoSpec.symm
      (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp only [l, Iso.symm_hom, Iso.refl_hom, Category.comp_id])
      (by simp only [r, b, Iso.symm_hom, Iso.refl_hom, Category.comp_id])
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
  have houter : IsPullback a g₁ f (l ≫ i) :=
    (IsPullback.of_hasPullback g₀ l).paste_horiz (IsPullback.of_hasPullback f i)
  let α : pullback g₀ l ⟶ pullback f t := pullback.lift a (g₁ ≫ r) (by
    exact houter.w.trans ((congrArg (fun z ↦ g₁ ≫ z) hbase.w).trans
      (Category.assoc g₁ r t).symm))
  have H : IsPullback α g₁ g r := by
    have ho : IsPullback (α ≫ pullback.fst f t) g₁ f (r ≫ t) := by
      rw [pullback.lift_fst, ← hbase.w]
      exact houter
    exact ho.of_right (by simp only [α, g, pullback.lift_snd])
      (IsPullback.of_hasPullback f t)
  letI : IsClosedImmersion r := by dsimp only [r, b]; infer_instance
  letI : Surjective r := by dsimp only [r, b]; infer_instance
  letI : IsClosedImmersion α := MorphismProperty.of_isPullback H.flip inferInstance
  let F : Arrow.mk g₁ ⟶ Arrow.mk g := Arrow.homMk α r H.w
  letI : IsClosedImmersion F.right := by change IsClosedImmersion r; infer_instance
  letI : Surjective F.right := by change Surjective r; infer_instance
  have hc := hf S hS l ι (fun j ↦ α ⁻¹ᵁ U j)
    (fun j ↦ (hU j).preimage α) (α.iSup_preimage_eq_top hcU)
  exact (nilBaseChange_tupleTotal_acyclic_iff g₁ g F H q hq p hp hR hS U hU).mpr hc

end SerrePositivity.AlgebraicGeometry
