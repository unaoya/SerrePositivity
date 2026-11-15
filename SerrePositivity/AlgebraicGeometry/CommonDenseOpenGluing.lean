module

public import SerrePositivity.AlgebraicGeometry.DenseImageOpenLifts
public import SerrePositivity.AlgebraicGeometry.SchemeImageDominance
public import Mathlib.AlgebraicGeometry.Gluing

/-!
概要：同じ稠密な共通の開で一致する射を、開被覆上で貼り合わせる。
方針：重なりへ共通の開を持ち上げ、分離性と scheme-theoretic な稠密性で一致を示す。
規約：基底上の射を保持し、対象の被約性は要求しない。
使われ方：C06 のチャート上の固有射の貼り合わせ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u v

/-- 準コンパクトで稠密な射の開部分への因子化は稠密。 -/
theorem isSchemeTheoreticallyDominant_of_open_factor
    {W V Z : Scheme.{u}} (j : W ⟶ Z) [QuasiCompact j]
    [IsSchemeTheoreticallyDominant j] (b : V ⟶ Z) [IsOpenImmersion b]
    (w : W ⟶ V) (h : w ≫ b = j) : IsSchemeTheoreticallyDominant w := by
  have H : Set.range j ⊆ Set.range b := by
    rintro _ ⟨x, rfl⟩
    exact ⟨w x, by simpa only [Scheme.Hom.comp_apply] using congrArg (fun k ↦ k x) h⟩
  have hw : w = IsOpenImmersion.lift b j H := by
    apply (cancel_mono b).mp
    rw [h, IsOpenImmersion.lift_fac]
  rw [hw]
  exact isSchemeTheoreticallyDominant_open_lift j b H

/-- 共通の稠密な開で一致する分離的な標的への射は、開被覆上で貼り合わさる。 -/
theorem exists_glued_map_of_common_dense_open
    {X Y S W : Scheme.{u}} (𝒰 : X.OpenCover.{v})
    (s : Y ⟶ S) [IsSeparated s] (x : X ⟶ S)
    (j : W ⟶ X) [QuasiCompact j] [IsSchemeTheoreticallyDominant j]
    (l : ∀ i, W ⟶ 𝒰.X i) (hl : ∀ i, l i ≫ 𝒰.f i = j)
    (f : ∀ i, 𝒰.X i ⟶ Y) (hf : ∀ i, f i ≫ s = 𝒰.f i ≫ x)
    (r : W ⟶ Y) (hr : ∀ i, l i ≫ f i = r) :
    ∃ a : X ⟶ Y, (∀ i, 𝒰.f i ≫ a = f i) ∧ a ≫ s = x := by
  have hcompat (i k : 𝒰.I₀) :
      pullback.fst (𝒰.f i) (𝒰.f k) ≫ f i = pullback.snd _ _ ≫ f k := by
    let T := pullback (𝒰.f i) (𝒰.f k)
    let b : T ⟶ X := pullback.fst (𝒰.f i) (𝒰.f k) ≫ 𝒰.f i
    let w : W ⟶ T := pullback.lift (l i) (l k) ((hl i).trans (hl k).symm)
    have hwb : w ≫ b = j := by
      dsimp [w, b]
      rw [pullback.lift_fst_assoc, hl i]
    haveI : IsOpenImmersion b := inferInstance
    haveI : IsSchemeTheoreticallyDominant w :=
      isSchemeTheoreticallyDominant_of_open_factor j b w hwb
    have hbase : (pullback.fst (𝒰.f i) (𝒰.f k) ≫ f i) ≫ s =
        (pullback.snd (𝒰.f i) (𝒰.f k) ≫ f k) ≫ s := by
      simp only [Category.assoc, hf, pullback.condition_assoc]
    have hcommon : w ≫ (pullback.fst (𝒰.f i) (𝒰.f k) ≫ f i) =
        w ≫ (pullback.snd (𝒰.f i) (𝒰.f k) ≫ f k) := by
      dsimp [w]
      rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, hr i, hr k]
    exact ext_of_isSchemeTheoreticallyDominant_of_isSeparated s hbase w hcommon
  let a := 𝒰.glueMorphisms f hcompat
  have hres (i : 𝒰.I₀) : 𝒰.f i ≫ a = f i := 𝒰.ι_glueMorphisms f hcompat i
  refine ⟨a, hres, ?_⟩
  apply 𝒰.hom_ext
  intro i
  rw [← Category.assoc, hres, hf]

end SerrePositivity.AlgebraicGeometry
