module
public import SerrePositivity.KST.SConstruction.DGStandardCubeNaturality
public import SerrePositivity.KST.SConstruction.DGStandardCoherentMap
public import SerrePositivity.InfinityCategories.DoldKanComparison.CoherentComparison
public import SerrePositivity.InfinityCategories.DGNerve.Functor

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
open DoldKanComparison
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} {E : Type w}
  [DGCategory A D] [DGCategory A E]

/-- 元の DK 比較の全単体データは、元の厳密 dg 関手の後合成と可換。 -/
lemma dgStandardCoherentSimplexData_post (F : DGFunctor A D E) {N : ℕ}
    (s : (doldKanCoherentNerve (R := A) (D := D)) _⦋N⦌) :
    coherentSimplexData (s.comp SSet (dgStandardEnrichedFunctor F)) =
      (coherentSimplexData s).map F := by
  apply DGNerve.SimplexData.ext
  · rfl
  · apply heq_of_eq
    funext I a b k hI ha hb hk
    dsimp only [coherentSimplexData, DGNerve.SimplexData.map]
    exact dgStandardCoherentCubeComponentAt_post F s _ _ k _

/-- 元の DK 比較の native HA 単体は、元の厳密 dg 関手の後合成と可換。 -/
lemma dgStandardCoherentSimplex_post (F : DGFunctor A D E) {N : ℕ}
    (s : (doldKanCoherentNerve (R := A) (D := D)) _⦋N⦌) :
    coherentSimplex (s.comp SSet (dgStandardEnrichedFunctor F)) =
      (coherentSimplex s).map F := by
  apply DGNerve.Simplex.ext
  exact dgStandardCoherentSimplexData_post F s

/-- 既存の全単体的 DK 比較は、厳密 dg 入力写像について自然。 -/
lemma dgCoherentComparison_naturality {B : Type v} [DGCategory A B] (F : DGFunctor A D B) :
    dgStandardCoherentMap F ≫ (coherentComparison (R := A) (D := B)) =
      (coherentComparison (R := A) (D := D)) ≫ dgNerve.map F := by
  ext n s
  exact dgStandardCoherentSimplex_post F s

end SerrePositivity.KST.SConstruction
