module
public import SerrePositivity.KST.SConstruction.SimplexSubsetLambdaInclusion
public import SerrePositivity.KST.SConstruction.SimplexDiagonalLambdaHom

/-! # 元の部分集合 cell の増大と入力写像の後合成
概要：元の部分集合 cell は元の Serre 増大を保ち、入力後合成でも同じ増大を回収する。
方針：元の実余モノイド射と Λ 増大 dg 関手の厳密自然性を使う。
規約：元の cube 次元・全 Hom を保持。使われ方：潰れる二点 HA 成分の単位回収。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の部分集合の実 Serre cell は、元の Hom 増大と cube 増大を厳密に可換にする。 -/
lemma simplexSubsetLambdaCellAt_augmentation {M : ℕ} (I : Finset (Fin (M + 1)))
    (a b : Fin (M + 1)) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) :
    simplexSubsetLambdaCellAt A I a b hI ha hb ≫
      (cubicalLambdaCounit.{u, 0} A (Δ[M] : SSet.{u})).map
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) =
      serreCubeAugmentation A (I.card - 2) :=
  (simplexSubsetLambdaCellComonoidAt A I a b hI ha hb).isComonHom_hom.hom_counit

/-- 元の入力写像の後合成も、元の同じ部分集合 cell の増大を保持する。 -/
lemma simplexSubsetLambdaCellAt_post_augmentation {M : ℕ} {K : SSet.{u}}
    (φ : (Δ[M] : SSet.{u}) ⟶ K) (I : Finset (Fin (M + 1)))
    (a b : Fin (M + 1)) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) :
    (simplexSubsetLambdaCellAt A I a b hI ha hb ≫ (cubicalLambdaMap A φ).map
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b)) ≫
      (cubicalLambdaCounit.{u, 0} A K).map
        (φ.app _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a)) (φ.app _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b)) =
      serreCubeAugmentation A (I.card - 2) := by
  have hc : (cubicalLambdaMap A φ).map (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) ≫
      (cubicalLambdaCounit.{u, 0} A K).map
        (φ.app _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a)) (φ.app _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b)) =
      (cubicalLambdaCounit.{u, 0} A (Δ[M] : SSet.{u})).map
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b) :=
    (cubicalLambdaMapComonoid A φ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b)).isComonHom_hom.hom_counit
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => simplexSubsetLambdaCellAt A I a b hI ha hb ≫ f) hc).trans
      (simplexSubsetLambdaCellAt_augmentation A I a b hI ha hb))

private lemma diagonal_map_heq {N : ℕ} {H : Complex A} (x y : Fin (N + 1)) (hxy : x = y)
    (f : H ⟶ homObject A (CubicalLambda A (Δ[N] : SSet.{u}))
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex x) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex y)) (g : H ⟶ 𝟙_ (Complex A))
    (hf : f ≫ (cubicalLambdaCounit.{u, 0} A (Δ[N] : SSet.{u})).map
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex x) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex y) = g) :
    HEq f (g ≫ eId (C := CubicalLambda A (Δ[N] : SSet.{u}))
      (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex y)) := by
  subst x
  apply heq_of_eq
  apply (cancel_mono ((cubicalLambdaCounit.{u, 0} A (Δ[N] : SSet.{u})).map
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex y) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex y))).mp
  exact hf.trans ((Category.assoc _ _ _).trans
    ((congrArg (fun h => g ≫ h) ((cubicalLambdaCounit.{u, 0} A (Δ[N] : SSet.{u})).map_id
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex y))).trans (Category.comp_id _))).symm

/-- 元の二端点が同じ像頂点なら、元の部分集合 cell の像は同じ増大と対角単位の合成。 -/
lemma simplexSubsetLambdaCellAt_post_diagonal_heq {M N : ℕ}
    (α : Fin (M + 1) →o Fin (N + 1)) (I : Finset (Fin (M + 1)))
    (a b : Fin (M + 1)) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI)) (hab : α a = α b) :
    HEq (simplexSubsetLambdaCellAt A I a b hI ha hb ≫
      (cubicalLambdaMap A (SSet.stdSimplex.map (SimplexCategory.Hom.mk α))).map
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex b))
      (serreCubeAugmentation A (I.card - 2) ≫
        eId (C := CubicalLambda A (Δ[N] : SSet.{u})) (Complex A) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.standardSimplexVertex (α b))) :=
  diagonal_map_heq A (α a) (α b) hab _ _
    (simplexSubsetLambdaCellAt_post_augmentation A
      (SSet.stdSimplex.map (SimplexCategory.Hom.mk α)) I a b hI ha hb)

end SerrePositivity.KST.SConstruction
