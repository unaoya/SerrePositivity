module
public import SerrePositivity.KST.SConstruction.SimplexHAIntervalOneTensor
public import SerrePositivity.KST.SConstruction.SimplexIntervalLambdaStandardComposition
public import SerrePositivity.KST.SConstruction.EnrichedHomCompositionComparison
public import SerrePositivity.KST.SConstruction.SimplexHAHomCompositionReduction

/-! # 元の全 HA Hom 族の実合成保存
概要：元の厳密二区間の逆 Hom 鎖射は合成を保ち、対角・逆向きも含む全三頂点へ広げる。
方針：元の Λ と HA の同じ右一面公式を照合し、可逆な区間 Hom・tensor 比較を消去。
規約：元の全 Hom・実合成・端点を保持。使われ方：native HA 単体からの実逆 dg 関手。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の厳密二区間の逆 Hom 鎖射は、元の同じ豊穣合成を厳密に保つ。 -/
lemma simplexHAIntervalHomMap_comp {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (a b c : Fin (N + 1)) (hab : a < b) (hbc : b < c) :
    eComp (C := CubicalLambda A (Δ[N] : SSet.{u})) (Complex A)
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex c) ≫
      simplexHAIntervalHomMap A s a c (hab.trans hbc) =
      (simplexHAIntervalHomMap A s a b hab ⊗ₘ simplexHAIntervalHomMap A s b c hbc) ≫
        eComp (Complex A) (s.obj a) (s.obj b) (s.obj c) := by
  let n := b.val - a.val - 1
  let m := c.val - b.val - 1
  let e := simplexIntervalLambdaHomIso A a b hab.le
  let f := simplexIntervalLambdaHomIso A b c hbc.le
  let g := simplexIntervalLambdaHomIso A a c (hab.le.trans hbc.le)
  let F := simplexHAIntervalHomMap A s a b hab
  let G := simplexHAIntervalHomMap A s b c hbc
  let H := simplexHAIntervalHomMap A s a c (hab.trans hbc)
  let d := eqToHom (congrArg (serreCubeComplex A)
    (simplexHAStrictInterval_split_dimension a b c hab hbc).symm)
  let q := (serreCubeRightFace A true n m).hom
  have h : (serreCubeTensorComposition A n m e.hom f.hom) ≫ H =
      serreCubeTensorComposition A n m (e.hom ≫ F) (f.hom ≫ G) := by
    calc
      _ = (q ≫ d ≫ g.hom) ≫ H :=
        congrArg (fun k => k ≫ H)
          (simplexIntervalLambdaHomIso_composition_one_tensor A a b c hab hbc)
      _ = q ≫ d ≫ (g.hom ≫ H) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun k => q ≫ k) (Category.assoc _ _ _))
      _ = q ≫ d ≫ simplexHAIntervalChainLift A s a c (hab.trans hbc) :=
        congrArg (fun k => q ≫ d ≫ k)
          (simplexHAIntervalHomMap_restrict A s a c (hab.trans hbc))
      _ = serreCubeTensorComposition A n m (simplexHAIntervalChainLift A s a b hab)
          (simplexHAIntervalChainLift A s b c hbc) :=
        simplexHAIntervalChainLift_one_tensor A s a b c hab hbc
      _ = _ := congrArg₂ (fun k l => serreCubeTensorComposition A n m k l)
        (simplexHAIntervalHomMap_restrict A s a b hab).symm
        (simplexHAIntervalHomMap_restrict A s b c hbc).symm
  exact enrichedHom_composition_of_tensor_comparison
    (V := Complex A) (C := CubicalLambda A (Δ[N] : SSet.{u})) (D := D)
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a : CubicalLambda A (Δ[N] : SSet.{u}))
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex c) (s.obj a) (s.obj b) (s.obj c)
    e f ((Comon.forget (Complex A)).mapIso (serreCubeTensorIso A n m)) F G H h

/-- 元の厳密三頂点の全 HA Hom 族は、元の同じ豊穣合成を厳密に保つ。 -/
lemma simplexHAHomMap_comp_strict {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (a b c : Fin (N + 1)) (hab : a < b) (hbc : b < c) :
    eComp (C := CubicalLambda A (Δ[N] : SSet.{u})) (Complex A)
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex c) ≫
      simplexHAHomMap A s a c =
      (simplexHAHomMap A s a b ⊗ₘ simplexHAHomMap A s b c) ≫
        eComp (Complex A) (s.obj a) (s.obj b) (s.obj c) := by
  simpa only [simplexHAHomMap_of_lt A s a b hab, simplexHAHomMap_of_lt A s b c hbc,
    simplexHAHomMap_of_lt A s a c (hab.trans hbc)] using
      simplexHAIntervalHomMap_comp A s a b c hab hbc

/-- 元の対角・逆向きも含む全三頂点で、元の全 HA Hom 族は実合成を厳密に保つ。 -/
lemma simplexHAHomMap_comp {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D N)
    (a b c : Fin (N + 1)) :
    eComp (C := CubicalLambda A (Δ[N] : SSet.{u})) (Complex A)
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex c) ≫
      simplexHAHomMap A s a c =
      (simplexHAHomMap A s a b ⊗ₘ simplexHAHomMap A s b c) ≫
        eComp (Complex A) (s.obj a) (s.obj b) (s.obj c) :=
  simplexHAHomMap_comp_of_strict A s (simplexHAHomMap_comp_strict A s) a b c

end SerrePositivity.KST.SConstruction
