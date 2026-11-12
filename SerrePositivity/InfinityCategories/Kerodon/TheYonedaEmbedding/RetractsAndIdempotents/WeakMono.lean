module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.TriangleKernel
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
概要：元の Ret の商から元の強い分裂の添字への標準比較は単射。
方針：商の二単体からの全射と、元の分裂二単体の全次数での核の分類を使う。
規約：元の長辺の商を保持し、inner anodyne 性はこの段階では主張しない。
使われ方：HTT 4.4.5.6 の元の Ret 部分複体との厳密な同定。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の長辺を潰す射には、元の端点を指定する切断がある。 -/
lemma longEdgeCollapse_section :
    stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.longEdgeCollapse.{u} = 𝟙 (Δ[0] : SSet.{u}) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  apply SSet.stdSimplex.ext
  intro i
  apply Fin.ext
  omega

/-- 元の長辺を潰す射は全射。 -/
instance longEdgeCollapse_epi : Epi _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.longEdgeCollapse.{u} :=
  epi_of_epi_fac longEdgeCollapse_section

/-- 元の二単体から Ret の商への標準射は全射。 -/
instance weakTriangle_epi : Epi _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakTriangle.{u} :=
  inferInstanceAs (Epi (pushout.inl (stdSimplex.δ (1 : Fin 3)) _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.longEdgeCollapse.{u}))

/-- 元の Ret の各単体は、元の二単体の単体の像として表せる。 -/
lemma weakTriangle_app_surjective (n : ℕ) :
    Function.Surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakTriangle.{u}.app (Opposite.op ⦋n⦌)) :=
  (CategoryTheory.epi_iff_surjective _).mp inferInstance

/-- 元の Ret の商から元の強い分裂の添字への標準比較は単射。 -/
instance weakComparison_mono : Mono _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakComparison.{u} := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨n⟩⟩
  apply (CategoryTheory.mono_iff_injective _).mpr
  intro x y h
  obtain ⟨a, rfl⟩ := weakTriangle_app_surjective n x
  obtain ⟨b, rfl⟩ := weakTriangle_app_surjective n y
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakTriangle ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakComparison).app (Opposite.op ⦋n⦌) a =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakTriangle ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakComparison).app (Opposite.op ⦋n⦌) b at h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakComparison_triangle] at h
  rcases _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingRetractionTriangle_kernel h with hab | ⟨ha, hb⟩
  · rw [hab]
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakTriangle_eq_of_avoids_one ha hb

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
