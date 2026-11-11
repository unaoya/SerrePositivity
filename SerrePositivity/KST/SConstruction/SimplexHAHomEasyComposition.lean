module
public import SerrePositivity.KST.SConstruction.SimplexHAHomMap
public import SerrePositivity.KST.SConstruction.EnrichedHomUnitComposition

/-! # 元の HA Hom 族の対角・逆向き因子を含む実合成
概要：元の対角を含む合成と、逆向き Hom を因子に持つ合成について保存を証明する。
方針：元の単位の実同型性、豊穣単位律、実零 Hom の tensor の零性を使う。
規約：元の全 Hom・実合成を保持。使われ方：厳密な三頂点の場合への合成保存の帰着。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の HA Hom 族は、元の左対角を含む実合成を保つ。 -/
lemma simplexHAHomMap_comp_left_diagonal {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (a c : Fin (N + 1)) :
    eComp (C := CubicalLambda A (Δ[N] : SSet.{u})) (Complex A)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex c) ≫
        simplexHAHomMap A s a c =
      (simplexHAHomMap A s a a ⊗ₘ simplexHAHomMap A s a c) ≫
        eComp (Complex A) (s.obj a) (s.obj a) (s.obj c) :=
  enrichedHom_left_unit_composition (V := Complex A) (C := CubicalLambda A (Δ[N] : SSet.{u}))
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex c) (s.obj a) (s.obj c)
    (simplexHAHomMap A s a a) (simplexHAHomMap A s a c) (simplexHAHomMap_id A s a)

/-- 元の HA Hom 族は、元の右対角を含む実合成を保つ。 -/
lemma simplexHAHomMap_comp_right_diagonal {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (a c : Fin (N + 1)) :
    eComp (C := CubicalLambda A (Δ[N] : SSet.{u})) (Complex A)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex c) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex c) ≫
        simplexHAHomMap A s a c =
      (simplexHAHomMap A s a c ⊗ₘ simplexHAHomMap A s c c) ≫
        eComp (Complex A) (s.obj a) (s.obj c) (s.obj c) :=
  enrichedHom_right_unit_composition (V := Complex A) (C := CubicalLambda A (Δ[N] : SSet.{u}))
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex c) (s.obj a) (s.obj c)
    (simplexHAHomMap A s a c) (simplexHAHomMap A s c c) (simplexHAHomMap_id A s c)

/-- 元の左因子が逆向き Hom なら、実零 tensor source から元の実合成保存を得る。 -/
lemma simplexHAHomMap_comp_left_reverse {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (a b c : Fin (N + 1)) (hba : b < a) :
    eComp (C := CubicalLambda A (Δ[N] : SSet.{u})) (Complex A)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex c) ≫
        simplexHAHomMap A s a c =
      (simplexHAHomMap A s a b ⊗ₘ simplexHAHomMap A s b c) ≫
        eComp (Complex A) (s.obj a) (s.obj b) (s.obj c) := by
  exact (Functor.map_isZero
    (tensorRight (homObject A (CubicalLambda A (Δ[N] : SSet.{u}))
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex c)))
        (simplexReverseLambdaHom_isZero A a b hba)).eq_of_src _ _

/-- 元の右因子が逆向き Hom なら、実零 tensor source から元の実合成保存を得る。 -/
lemma simplexHAHomMap_comp_right_reverse {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (a b c : Fin (N + 1)) (hcb : c < b) :
    eComp (C := CubicalLambda A (Δ[N] : SSet.{u})) (Complex A)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex c) ≫
        simplexHAHomMap A s a c =
      (simplexHAHomMap A s a b ⊗ₘ simplexHAHomMap A s b c) ≫
        eComp (Complex A) (s.obj a) (s.obj b) (s.obj c) := by
  exact (Functor.map_isZero
    (tensorLeft (homObject A (CubicalLambda A (Δ[N] : SSet.{u}))
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b)))
        (simplexReverseLambdaHom_isZero A b c hcb)).eq_of_src _ _

end SerrePositivity.KST.SConstruction
