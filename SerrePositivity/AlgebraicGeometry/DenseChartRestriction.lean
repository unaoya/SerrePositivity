module

public import SerrePositivity.AlgebraicGeometry.CommonDenseOpenGluing
public import Mathlib.AlgebraicGeometry.Restrict

/-!
概要：共通の稠密な開による比較を、貼り合わせた射のチャートの逆像へ延ばす。
方針：逆像の開へ共通の開を持ち上げ、分離性で二つの射を一致させる。
規約：基底上の可換式を保ち、被約性は要求しない。
使われ方：C06 の局所の固有射が実際の底変換であることの確認。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 共通の稠密な開でのチャートへの射の一致は、チャートの逆像全体での一致を与える。 -/
theorem restrict_eq_of_common_dense_chart
    {T X W P S : Scheme.{u}} (a : T ⟶ X) (U : X.Opens)
    (s : X ⟶ S) (q : P ⟶ S) [IsSeparated q]
    (p : T ⟶ P) (e : U.toScheme ⟶ P)
    (hp : p ≫ q = a ≫ s) (he : e ≫ q = U.ι ≫ s)
    (j : W ⟶ T) [QuasiCompact j] [IsSchemeTheoreticallyDominant j]
    (l : W ⟶ U.toScheme) (hla : l ≫ U.ι = j ≫ a)
    (hjp : j ≫ p = l ≫ e) :
    (a ⁻¹ᵁ U).ι ≫ p = (a ∣_ U) ≫ e := by
  let V := a ⁻¹ᵁ U
  have H : Set.range j ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change a (j x) ∈ U
    have hx : (l x).val = a (j x) := by
      simpa only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] using congrArg (fun k ↦ k x) hla
    rw [← hx]
    exact (l x).property
  let w : W ⟶ V.toScheme := IsOpenImmersion.lift V.ι j H
  have hw : w ≫ V.ι = j := IsOpenImmersion.lift_fac _ _ _
  haveI : IsSchemeTheoreticallyDominant w :=
    isSchemeTheoreticallyDominant_open_lift j V.ι H
  have hwl : w ≫ (a ∣_ U) = l := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hw, hla]
  have hbase : (V.ι ≫ p) ≫ q = ((a ∣_ U) ≫ e) ≫ q := by
    rw [Category.assoc, hp, Category.assoc, he,
      ← Category.assoc (a ∣_ U), morphismRestrict_ι, Category.assoc]
  have hcommon : w ≫ (V.ι ≫ p) = w ≫ ((a ∣_ U) ≫ e) := by
    rw [← Category.assoc, hw, hjp, ← Category.assoc, hwl]
  exact ext_of_isSchemeTheoreticallyDominant_of_isSeparated q hbase w hcommon

/-- チャートとの比較で、指定した開部分の像が貼り合わせた射の逆像に一致する。 -/
theorem range_chart_eq_preimage_of_dense_comparison
    {Z T X V P : Scheme.{u}} (a : T ⟶ X) (U : X.Opens)
    (t : T ⟶ Z) [IsOpenImmersion t] (b : V ⟶ Z) (c : V ⟶ T)
    (hct : c ≫ t = b) (r : V ⟶ U.toScheme) (hca : c ≫ a = r ≫ U.ι)
    (p : Z ⟶ P) (e : U.toScheme ⟶ P)
    (hrange : Set.range b = p ⁻¹' Set.range e)
    (hcompare : (a ⁻¹ᵁ U).ι ≫ t ≫ p = (a ∣_ U) ≫ e) :
    Set.range c = (a ⁻¹ᵁ U : Set T) := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    change a (c v) ∈ U
    have hv : a (c v) = (r v).val := by
      simpa only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] using congrArg (fun k ↦ k v) hca
    rw [hv]
    exact (r v).property
  · intro hx
    let y : (a ⁻¹ᵁ U).toScheme := ⟨x, hx⟩
    have hy : p (t x) = e ((a ∣_ U) y) := by
      simpa only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply, y] using congrArg (fun k ↦ k y) hcompare
    have hb : t x ∈ Set.range b := by
      rw [hrange]
      exact ⟨(a ∣_ U) y, hy.symm⟩
    obtain ⟨v, hv⟩ := hb
    refine ⟨v, t.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hct]
    exact hv

end SerrePositivity.AlgebraicGeometry
