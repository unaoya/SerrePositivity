module
public import SerrePositivity.KST.SConstruction.SimplexHAIntervalComposition
public import SerrePositivity.KST.SConstruction.SimplexHAOriginalHomMap

/-! # 元の native HA 単体からの実逆 dg 関手
概要：元の全 Λ 対象と全 Hom の復元族を、単位・全合成を保つ実 dg 関手に束ねる。
方針：元の頂点番号の全単射で、証明済みの全三頂点の合成保存を移す。
規約：元の全対象・Hom と厳密 dg 後合成を保持。使われ方：native dg nerve と Λ の比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の Λ の全対象・全 Hom の復元族は、元の同じ実豊穣合成を厳密に保つ。 -/
lemma simplexHAOriginalHomMap_comp {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (x y z : CubicalLambda A (Δ[N] : SSet.{u})) :
    eComp (Complex A) x y z ≫ simplexHAOriginalHomMap A s x z =
      (simplexHAOriginalHomMap A s x y ⊗ₘ simplexHAOriginalHomMap A s y z) ≫
        eComp (Complex A) (simplexHAInverseObj A s x) (simplexHAInverseObj A s y)
          (simplexHAInverseObj A s z) := by
  obtain ⟨a, rfl⟩ := (simplexLambdaVertexEquiv A N).surjective x
  obtain ⟨b, rfl⟩ := (simplexLambdaVertexEquiv A N).surjective y
  obtain ⟨c, rfl⟩ := (simplexLambdaVertexEquiv A N).surjective z
  have hL := congrArg (fun f => eComp
    (C := CubicalLambda A (Δ[N] : SSet.{u})) (Complex A)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex c) ≫ f)
        (simplexHAOriginalHomMap_vertices A s a c)
  have hR := congrArg₂ (fun f g => (f ⊗ₘ g) ≫
    eComp (Complex A) (s.obj a) (s.obj b) (s.obj c))
      (simplexHAOriginalHomMap_vertices A s a b) (simplexHAOriginalHomMap_vertices A s b c)
  exact hL.trans ((simplexHAHomMap_comp A s a b c).trans hR.symm)

/-- 元の全 native HA 単体は、元の Λ 標準単体からの実 dg 関手を定める。 -/
def simplexHAInverseFunctor {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N) :
    DGFunctor A (CubicalLambda A (Δ[N] : SSet.{u})) D where
  obj := simplexHAInverseObj A s
  map := simplexHAOriginalHomMap A s
  map_id := simplexHAOriginalHomMap_id A s
  map_comp := simplexHAOriginalHomMap_comp A s

/-- 元の番号の頂点では、実逆 dg 関手の対象は同じ native HA 対象。 -/
lemma simplexHAInverseFunctor_obj_vertex {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (a : Fin (N + 1)) : (simplexHAInverseFunctor A s).obj (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) = s.obj a :=
  rfl

/-- 元の番号の頂点間では、実逆 dg 関手は同じ native HA Hom 鎖射を回収する。 -/
lemma simplexHAInverseFunctor_map_vertices {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (a b : Fin (N + 1)) :
    (simplexHAInverseFunctor A s).map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) =
      simplexHAHomMap A s a b := simplexHAOriginalHomMap_vertices A s a b

/-- 元の実逆 dg 関手は、元の厳密 dg 後合成と厳密に可換。 -/
lemma simplexHAInverseFunctor_post {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    {E : Type w} [DGCategory A E] (F : DGFunctor A D E) :
    simplexHAInverseFunctor A (s.map F) = DGFunctor.comp (simplexHAInverseFunctor A s) F := by
  refine EnrichedFunctor.ext (Complex A)
    (F := simplexHAInverseFunctor A (s.map F))
    (G := DGFunctor.comp (simplexHAInverseFunctor A s) F) (fun _ => rfl) ?_
  intro x y
  exact (Category.comp_id _).trans (simplexHAOriginalHomMap_post A s F x y)

end SerrePositivity.KST.SConstruction
