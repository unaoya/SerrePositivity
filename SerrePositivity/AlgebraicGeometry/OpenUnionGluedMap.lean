module

public import SerrePositivity.AlgebraicGeometry.SchemeOpenUnionCover
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
概要：実際の開包含の像の和に、共通の稠密な開で一致する射を貼り合わせる。
方針：元の成分による和の被覆に既存の稠密な開の貼り合わせを適用する。
規約：和への開包含、共通の開と各成分の射、基底上の可換式を保持する。
使われ方：C06 の元の対象への射の構成。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u v

/-- 共通の稠密な開で一致する射を、実際の開部分の和へ貼り合わせる。 -/
theorem exists_open_union_glued_map
    {Z Y S W : Scheme.{u}} {I : Type v} [Nonempty I]
    (V : I → Scheme.{u}) (b : ∀ i, V i ⟶ Z) [∀ i, IsOpenImmersion (b i)]
    (s : Y ⟶ S) [IsSeparated s] (z : Z ⟶ S)
    (j : W ⟶ Z) [IsOpenImmersion j] [QuasiCompact j]
    [IsSchemeTheoreticallyDominant j]
    (l : ∀ i, W ⟶ V i) (hl : ∀ i, l i ≫ b i = j)
    (f : ∀ i, V i ⟶ Y) (hf : ∀ i, f i ≫ s = b i ≫ z)
    (r : W ⟶ Y) (hr : ∀ i, l i ≫ f i = r) :
    ∃ (T : Scheme.{u}) (t : T ⟶ Z) (c : ∀ i, V i ⟶ T)
      (w : W ⟶ T) (a : T ⟶ Y),
      IsOpenImmersion t ∧ (∀ i, IsOpenImmersion (c i)) ∧
      IsOpenImmersion w ∧ IsSchemeTheoreticallyDominant w ∧
      (∀ i, c i ≫ t = b i) ∧ w ≫ t = j ∧
      (∀ i, l i ≫ c i = w) ∧ (∀ i, c i ≫ a = f i) ∧
      a ≫ s = t ≫ z ∧ w ≫ a = r ∧
      (∀ x : T, ∃ i, x ∈ Set.range (c i)) := by
  classical
  let U := ⨆ i, (b i).opensRange
  let 𝒰 := schemeOpenUnionCover V b
  have hfac (i : I) : 𝒰.f i ≫ U.ι = b i := schemeOpenUnionCover_fac V b i
  let i₀ : I := Classical.choice inferInstance
  have H : Set.range j ⊆ Set.range U.ι := by
    rintro _ ⟨x, rfl⟩
    apply range_subset_open_union V b i₀
    refine ⟨l i₀ x, ?_⟩
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun k ↦ k x) (hl i₀)
  let w : W ⟶ U.toScheme := IsOpenImmersion.lift U.ι j H
  have hwt : w ≫ U.ι = j := IsOpenImmersion.lift_fac _ _ _
  haveI : IsOpenImmersion w := isOpenImmersion_open_lift j U.ι H
  haveI : IsSchemeTheoreticallyDominant w :=
    isSchemeTheoreticallyDominant_open_lift j U.ι H
  haveI : QuasiCompact (w ≫ U.ι) := by rw [hwt]; infer_instance
  haveI : QuasiCompact w := QuasiCompact.of_comp w U.ι
  have hlc (i : I) : l i ≫ 𝒰.f i = w := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, hfac, hl, hwt]
  have hf' (i : I) : f i ≫ s = 𝒰.f i ≫ (U.ι ≫ z) := by
    rw [← Category.assoc, hfac]
    exact hf i
  obtain ⟨a, ha, hbase⟩ := exists_glued_map_of_common_dense_open
    𝒰 s (U.ι ≫ z) w l hlc f hf' r hr
  refine ⟨U.toScheme, U.ι, 𝒰.f, w, a, inferInstance, (fun i ↦ inferInstance),
    inferInstance, inferInstance, hfac, hwt, hlc, ha, hbase, ?_, ?_⟩
  · rw [← hlc i₀, Category.assoc, ha, hr]
  · exact fun x ↦ 𝒰.exists_eq x

end SerrePositivity.AlgebraicGeometry
