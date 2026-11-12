module
public import SerrePositivity.KST.SConstruction.DGStandardCubeNaturality
public import SerrePositivity.KST.SConstruction.DGStandardCoherentMap
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentComparison
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor

/-! # 既存 DK 比較の厳密 dg 入力自然性
概要：標準 DK coherent nerve と native dg nerve の比較は、元の厳密 dg 関手で自然。
方針：元の全最大旗の評価自然性を、全有限頂点集合の HA 成分へ適用する。
規約：全対象・全 Hom・全作用素を保持。使われ方：native tensor と既存 DK の比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} {E : Type w}
  [DGCategory A D] [DGCategory A E]

/-- 元の DK 比較の全単体データは、元の厳密 dg 関手の後合成と可換。 -/
lemma dgStandardCoherentSimplexData_post (F : DGFunctor A D E) {N : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := A) (D := D)) _⦋N⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplexData (s.comp SSet (dgStandardEnrichedFunctor F)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplexData s).map F := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
  · rfl
  · apply heq_of_eq
    funext I a b k hI ha hb hk
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplexData, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.map]
    exact dgStandardCoherentCubeComponentAt_post F s _ _ k _

/-- 元の DK 比較の native HA 単体は、元の厳密 dg 関手の後合成と可換。 -/
lemma dgStandardCoherentSimplex_post (F : DGFunctor A D E) {N : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := A) (D := D)) _⦋N⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplex (s.comp SSet (dgStandardEnrichedFunctor F)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplex s).map F := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact dgStandardCoherentSimplexData_post F s

/-- 既存の全単体的 DK 比較は、厳密 dg 入力写像について自然。 -/
lemma dgCoherentComparison_naturality {B : Type v} [DGCategory A B] (F : DGFunctor A D B) :
    dgStandardCoherentMap F ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := A) (D := B)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := A) (D := D)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F := by
  ext n s
  exact dgStandardCoherentSimplex_post F s

end SerrePositivity.KST.SConstruction
