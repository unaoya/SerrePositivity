module

public import SerrePositivity.BhattScholze.Prismatic.CrystallineLocalizationLift
import all SerrePositivity.BhattScholze.Prismatic.CrystallineSiteBasic
import all SerrePositivity.BhattScholze.Prismatic.CrystallineSiteLocalization

/-!
# 結晶主開被覆の基底変換による細分

## 概要
任意の厚化の射に沿って、有限主開被覆を標準主開被覆で細分する。

## 方針
被覆を定める元を写し、局所化の普遍性で元の各開への射を作る。

## 規約
環の向きで記述する。サイトでは矢印を反転する。

## 使われ方
Berthelot III.4、Stacks 07HN。Zariski coverage の引き戻し公理。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic
variable {p : ℕ} {k : Type u} [CommRing k] {J : Ideal k} {γ : DividedPowers J}
variable {R : Type u} [CommRing R] [Algebra (k ⧸ J) R] {κ : Cardinal.{u}}

/-- 主開被覆は任意の厚化の射に沿って主開被覆による細分を持つ。 -/
theorem crysZariski_refinement (hκ : Cardinal.aleph0 ≤ κ)
    {ι : Type u} [Finite ι] {X Z : CrysOver p γ R κ}
    (Y : ι → CrysOver p γ R κ) (f : ∀ i, X ⟶ Y i)
    (hf : CrysOver.IsZariskiFamily Y f) (h : X ⟶ Z) :
    ∃ (W : ι → CrysOver p γ R κ) (a : ∀ i, Z ⟶ W i),
      CrysOver.IsZariskiFamily W a ∧
        ∃ b : ∀ i, Y i ⟶ W i, ∀ i, f i ≫ b i = h ≫ a i := by
  obtain ⟨g, hg, hl⟩ := hf
  let t : ι → Z.B := fun i => h.toAlgHom (g i)
  have ht : Ideal.span (Set.range t) = ⊤ := by
    have he : h.toAlgHom.toRingHom '' Set.range g = Set.range t := by
      ext z
      simp only [Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨g i, ⟨i, rfl⟩, rfl⟩
    rw [← he, ← Ideal.map_span, hg, Ideal.map_top]
  let W : ι → CrysOver p γ R κ := fun i => crysAway Z (t i) hκ
  let a : ∀ i, Z ⟶ W i := fun i => crysAwayHom Z (t i) hκ
  refine ⟨W, a, crysAway_isZariskiFamily Z hκ t ht, ?_⟩
  have hu (i : ι) : IsUnit ((h ≫ a i).toAlgHom (g i)) := by
    change IsUnit (algebraMap Z.B (Localization.Away (t i)) (t i))
    exact IsLocalization.Away.algebraMap_isUnit (t i)
  let b : ∀ i, Y i ⟶ W i := fun i =>
    crysLocalizationLift (f i) (g i) (hl i).1 (hl i).2 (h ≫ a i) (hu i)
  exact ⟨b, fun i => crysLocalizationLift_comp (f i) (g i) (hl i).1 (hl i).2
    (h ≫ a i) (hu i)⟩

end SerrePositivity.BhattScholze.Prismatic
