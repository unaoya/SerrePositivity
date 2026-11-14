module

public import SerrePositivity.AlgebraicGeometry.CommonDenseOpenGluing

/-!
概要：実際の開包含の像の和を、元の成分で被覆する。
方針：像の和への lift を使い、各点が元の成分から来ることを保つ。
規約：被覆の各成分は元のスキームそのもの。
使われ方：C06 のグラフ閉包内の開部分の和と局所射の貼り合わせ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits TopologicalSpace
universe u v

/-- 開包含の族の像の和への、各成分の像の包含。 -/
theorem range_subset_open_union {Z : Scheme.{u}} {I : Type v}
    (V : I → Scheme.{u}) (b : ∀ i, V i ⟶ Z) [∀ i, IsOpenImmersion (b i)] (i : I) :
    Set.range (b i) ⊆ Set.range (⨆ k, (b k).opensRange).ι := by
  rw [Scheme.Opens.range_ι]
  exact le_iSup (fun k ↦ (b k).opensRange) i

/-- 開包含の像の和を、元の成分そのもので被覆する。 -/
def schemeOpenUnionCover {Z : Scheme.{u}} {I : Type v}
    (V : I → Scheme.{u}) (b : ∀ i, V i ⟶ Z) [∀ i, IsOpenImmersion (b i)] :
    (⨆ i, (b i).opensRange).toScheme.OpenCover.{v} where
  I₀ := I
  X := V
  f i := IsOpenImmersion.lift (⨆ k, (b k).opensRange).ι (b i)
    (range_subset_open_union V b i)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, ?_⟩
    · obtain ⟨i, hi⟩ := Opens.mem_iSup.mp x.property
      obtain ⟨y, hy⟩ := Scheme.Hom.mem_opensRange.mp hi
      refine ⟨i, y, ?_⟩
      apply (⨆ k, (b k).opensRange).ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, IsOpenImmersion.lift_fac]
      exact hy
    · intro i
      exact isOpenImmersion_open_lift (b i) (⨆ k, (b k).opensRange).ι
        (range_subset_open_union V b i)

/-- 和の被覆の各射は、元の開包含に戻る。 -/
theorem schemeOpenUnionCover_fac {Z : Scheme.{u}} {I : Type v}
    (V : I → Scheme.{u}) (b : ∀ i, V i ⟶ Z) [∀ i, IsOpenImmersion (b i)] (i : I) :
    (schemeOpenUnionCover V b).f i ≫ (⨆ k, (b k).opensRange).ι = b i :=
  IsOpenImmersion.lift_fac _ _ _

end SerrePositivity.AlgebraicGeometry
