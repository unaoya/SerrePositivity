module

public import SerrePositivity.InfinityCategories.Core.Idempotent.TriangleKernel
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
概要：元の Ret の商から元の強い分裂の添字への標準比較は単射。
方針：商の二単体からの全射と、元の分裂二単体の全次数での核の分類を使う。
規約：元の長辺の商を保持し、inner anodyne 性はこの段階では主張しない。
使われ方：HTT 4.4.5.6 の元の Ret 部分複体との厳密な同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の長辺を潰す射には、元の端点を指定する切断がある。 -/
lemma longEdgeCollapse_section :
    stdSimplex.δ (0 : Fin 2) ≫ longEdgeCollapse.{u} = 𝟙 (Δ[0] : SSet.{u}) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  apply SSet.stdSimplex.ext
  intro i
  apply Fin.ext
  omega

/-- 元の長辺を潰す射は全射。 -/
instance longEdgeCollapse_epi : Epi longEdgeCollapse.{u} :=
  epi_of_epi_fac longEdgeCollapse_section

/-- 元の二単体から Ret の商への標準射は全射。 -/
instance weakTriangle_epi : Epi weakTriangle.{u} :=
  inferInstanceAs (Epi (pushout.inl (stdSimplex.δ (1 : Fin 3)) longEdgeCollapse.{u}))

/-- 元の Ret の各単体は、元の二単体の単体の像として表せる。 -/
lemma weakTriangle_app_surjective (n : ℕ) :
    Function.Surjective (weakTriangle.{u}.app (Opposite.op ⦋n⦌)) :=
  (CategoryTheory.epi_iff_surjective _).mp inferInstance

/-- 元の Ret の商から元の強い分裂の添字への標準比較は単射。 -/
instance weakComparison_mono : Mono weakComparison.{u} := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨n⟩⟩
  apply (CategoryTheory.mono_iff_injective _).mpr
  intro x y h
  obtain ⟨a, rfl⟩ := weakTriangle_app_surjective n x
  obtain ⟨b, rfl⟩ := weakTriangle_app_surjective n y
  change (weakTriangle ≫ weakComparison).app (Opposite.op ⦋n⦌) a =
    (weakTriangle ≫ weakComparison).app (Opposite.op ⦋n⦌) b at h
  rw [weakComparison_triangle] at h
  rcases walkingRetractionTriangle_kernel h with hab | ⟨ha, hb⟩
  · rw [hab]
  · exact weakTriangle_eq_of_avoids_one ha hb

end SerrePositivity.InfinityCategories.F2.Idempotent
