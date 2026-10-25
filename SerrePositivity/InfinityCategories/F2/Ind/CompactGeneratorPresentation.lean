module

public import SerrePositivity.InfinityCategories.F2.Ind.CompactGenerationComparison

/-!
概要：任意の元の Ind 対象を、compact 部分からの小さい filtered 余極限で表示する。
方針：元の Yoneda 密度余錐を、生成同値と compact 包含の厳密な合成式で読む。
規約：添字・元の C の図式・同じ余錐頂点を保持し、安定性や交換を仮定しない。
使われ方：I-2 e の compact 生成、および K-B の生成元の比較。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) [Fact κ.IsRegular] {C : SSet.{u}} [Quasicategory C]

/-- 同じ Ind 頂点そのものは、生成同値の compact 像の小さい κ-filtered 余極限。 -/
lemma indVertex_has_compactGeneratorPresentation (hC : Idempotent.IsIdempotentComplete C)
    (x : (IndInfinity κ C) _⦋0⦌) :
    ∃ (I : SSet.{u}) (hI : Quasicategory I),
      letI := hI
      IsKappaFiltered κ I ∧ ∃ a : I ⟶ C,
        ∃ c : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map a ≫
          (compactGenerationEquivalence κ hC).hom ≫
          Compact.kappaCompactInclusion.{u, u + 1} κ (IndInfinity κ C)),
          c.vertex = x ∧ IsColimitCone c := by
  rw [compactGenerationEquivalence_inclusion]
  exact indVertex_has_filteredYonedaPresentation κ x

/-- 元の生成同値の各像を Ind に含めると、その同じ頂点は κ-compact。 -/
lemma compactGenerationEquivalence_image_isKappaCompact
    (hC : Idempotent.IsIdempotentComplete C)
    (x : ((SSet.uliftFunctor.{u + 1, u}).obj C) _⦋0⦌) :
    Compact.IsKappaCompact.{u, u + 1} κ
      (((compactGenerationEquivalence κ hC).hom ≫
        Compact.kappaCompactInclusion.{u, u + 1} κ (IndInfinity κ C)).app _ x) := by
  rw [compactGenerationEquivalence_inclusion]
  rcases x with ⟨x⟩
  exact Compact.indYoneda_isKappaCompact κ x

end SerrePositivity.InfinityCategories.F2.Ind
