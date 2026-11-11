module
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceSimplexMaps
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplexIntervalMap
public import SerrePositivity.KST.SConstruction.CubicalLambda
public import SerrePositivity.KST.SConstruction.CubicalSerreAdjunction
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-! # 元の標準単体の逆向き端点の零 Hom
概要：元の b<a の間の cubical Hom は始対象、Λ の Hom 複体は零対象である。
方針：元の全 necklace 図式の空性と、元の Serre 鎖関手の余極限保存を使う。
規約：元の図式と Hom 複体を保持。使われ方：native dg 標準単体の全 Hom の比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits Simplicial SSet
open SerrePositivity.DifferentialGraded

/-- 元の逆向き二端点の間の cubical Hom は、元の空な図式の余極限である始対象。 -/
def simplexReverseCubicalMapping_isInitial {n : ℕ} (a b : Fin (n + 1)) (hba : b < a) :
    IsInitial (necklaceCubicalMapping (Δ[n] : SSet.{u})
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b)) := by
  let : IsEmpty (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn (Δ[n] : SSet.{u})
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b)) := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInSimplex_isEmpty hba
  exact (isColimitEquivIsInitialOfIsEmpty CubicalSet.{u} (colimit.cocone
    (necklaceCubicalDiagram (Δ[n] : SSet.{u})
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b)))) (colimit.isColimit _)

/-- 元の逆向き二端点の間の Λ の Hom は、元の Serre 鎖の始対象。 -/
def simplexReverseLambdaHom_isInitial (A : Type u) [CommRing A]
    {n : ℕ} (a b : Fin (n + 1)) (hba : b < a) :
    IsInitial (homObject A (CubicalLambda A (Δ[n] : SSet.{u}))
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b)) :=
  IsInitial.isInitialObj (cubicalSerreChains A) _ (simplexReverseCubicalMapping_isInitial a b hba)

/-- 元の逆向き二端点の間の Λ の Hom 複体は零対象。 -/
lemma simplexReverseLambdaHom_isZero (A : Type u) [CommRing A]
    {n : ℕ} (a b : Fin (n + 1)) (hba : b < a) :
    IsZero (homObject A (CubicalLambda A (Δ[n] : SSet.{u}))
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b)) :=
  (simplexReverseLambdaHom_isInitial A a b hba).isZero

end SerrePositivity.KST.SConstruction
